package vm

import (
	"bufio"
	"database/sql"
	"encoding/base64"
	"encoding/hex"
	"fmt"
	"io"
	"net"
	"noxy-vm/internal/ast"
	"noxy-vm/internal/chunk"
	"noxy-vm/internal/compiler"
	"noxy-vm/internal/lexer"
	"noxy-vm/internal/parser"
	"noxy-vm/internal/stdlib"
	"noxy-vm/internal/value"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"sync"
	"time"

	_ "modernc.org/sqlite"
)

const StackMax = 2048
const FramesMax = 64

func (vm *VM) runtimeError(c *chunk.Chunk, ip int, format string, args ...interface{}) error {
	line := 0
	file := "?"
	if c != nil {
		file = c.FileName
		if ip > 0 && ip <= len(c.Lines) {
			line = c.Lines[ip-1]
		}
	}
	msg := fmt.Sprintf(format, args...)
	return fmt.Errorf("[%s:line %d] %s", file, line, msg)
}

type CallFrame struct {
	Closure *value.ObjClosure
	IP      int
	Slots   int                    // Offset in stack where this frame's locals start
	Globals map[string]value.Value // Globals visible to this frame
}

type SharedState struct {
	Globals     map[string]value.Value // Global variables/functions
	Modules     map[string]value.Value // Cached modules (Name -> ObjMap)
	GlobalsLock sync.RWMutex

	// Shared Network Resources
	NetListeners map[int]net.Listener
	NetConns     map[int]net.Conn
	NextNetID    int
	NetLock      sync.Mutex

	// Shared Database Resources
	DbHandles   map[int]*sql.DB
	StmtHandles map[int]*sql.Stmt
	StmtParams  map[int]map[int]interface{}
	NextDbID    int
	NextStmtID  int
	DbLock      sync.Mutex
}

type VM struct {
	frames       [FramesMax]*CallFrame
	frameCount   int
	currentFrame *CallFrame

	chunk *chunk.Chunk // Removed, accessed via frame
	ip    int          // Removed, accessed via frame (or cached)

	stack    [StackMax]value.Value
	stackTop int

	shared *SharedState
	Config VMConfig

	// IO Management
	openFiles map[int64]*os.File
	nextFD    int64

	// Net Management (Moved to SharedState)
	netBufferedData  map[int][]byte   // For peeked data during select (Local to thread/VM?)
	netBufferedConns map[int]net.Conn // For peeked accepts (Local to thread/VM?)
	// netListeners, netConns, nextNetID removed from VM

	LastPopped value.Value

	openUpvalues *value.ObjUpvalue // Head of linked list of open upvalues
}

type VMConfig struct {
	RootPath string
	SafeMode bool
}

func New() *VM {
	// Default to SafeMode=true for this branch as requested
	return NewWithConfig(VMConfig{RootPath: ".", SafeMode: true})
}

func NewWithConfig(cfg VMConfig) *VM {
	shared := &SharedState{
		Globals:      make(map[string]value.Value),
		Modules:      make(map[string]value.Value),
		NetListeners: make(map[int]net.Listener),
		NetConns:     make(map[int]net.Conn),
		NextNetID:    1,
		DbHandles:    make(map[int]*sql.DB),
		StmtHandles:  make(map[int]*sql.Stmt),
		StmtParams:   make(map[int]map[int]interface{}),
		NextDbID:     1,
		NextStmtID:   1,
	}
	return NewWithShared(shared, cfg)
}

func NewWithShared(shared *SharedState, cfg VMConfig) *VM {
	vm := &VM{
		shared:    shared,
		Config:    cfg,
		openFiles: make(map[int64]*os.File),
		nextFD:    1,

		netBufferedData:  make(map[int][]byte),
		netBufferedConns: make(map[int]net.Conn),
	}

	// Define 'print' native
	vm.DefineNative("print", func(args []value.Value) value.Value {
		var parts []string
		for _, arg := range args {
			parts = append(parts, arg.String())
		}
		fmt.Println(strings.Join(parts, " "))
		return value.NewNull()
	})

	// Concurrency Primitives
	vm.DefineNative("spawn", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewNull()
		}
		fnVal := args[0]
		if fnVal.Type != value.VAL_FUNCTION {
			// For now only support script functions
			// Native functions in spawn? Maybe later.
			fmt.Println("Runtime Error: spawn expects a function")
			return value.NewNull()
		}

		threadArgs := args[1:]

		// Create new VM thread sharing state
		threadVM := NewWithShared(vm.shared, vm.Config)

		// Setup execution
		var closure *value.ObjClosure
		if cl, ok := fnVal.Obj.(*value.ObjClosure); ok {
			closure = cl
		} else if fn, ok := fnVal.Obj.(*value.ObjFunction); ok {
			closure = &value.ObjClosure{Function: fn, Upvalues: []*value.ObjUpvalue{}}
		} else {
			fmt.Println("Runtime Error: spawn expects a function or closure")
			return value.NewNull()
		}

		fnObj := closure.Function

		// Check arity
		if len(threadArgs) != fnObj.Arity {
			fmt.Printf("Runtime Error: spawn expected %d args, got %d\n", fnObj.Arity, len(threadArgs))
			return value.NewNull()
		}

		// Push Function (Stack slot 0)
		threadVM.push(fnVal)

		// Push Args
		for _, arg := range threadArgs {
			threadVM.push(arg)
		}

		// Create Frame
		frame := &CallFrame{
			Closure: closure,
			IP:      0,
			Slots:   0,
			Globals: nil,
		}

		// Map closure globals if present?
		// If fnObj.Globals is likely module map or nil (for Main).
		// We should respect it.
		frame.Globals = fnObj.Globals

		threadVM.frames[0] = frame
		threadVM.frameCount = 1
		threadVM.currentFrame = frame

		// Launch Goroutine
		go func() {
			defer func() {
				if r := recover(); r != nil {
					fmt.Printf("Thread Panic: %v\n%s", r, debug.Stack())
				}
			}()
			err := threadVM.run(1) // Run until finished (frame 0 popped)
			if err != nil {
				fmt.Printf("Thread Error: %v\n", err)
			}
		}()

		return value.NewNull()
	})

	vm.DefineNative("make_chan", func(args []value.Value) value.Value {
		size := 0
		if len(args) > 0 {
			if args[0].Type == value.VAL_INT {
				size = int(args[0].AsInt)
			}
		}
		return value.NewChannel(size)
	})

	vm.DefineNative("chan_send", func(args []value.Value) value.Value {
		if len(args) != 2 {
			return value.NewNull()
		}
		if args[0].Type != value.VAL_CHANNEL {
			return value.NewNull()
		}
		ch := args[0].Obj.(*value.ObjChannel).Chan
		ch <- args[1]
		return args[1]
	})

	vm.DefineNative("chan_close", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		if args[0].Type != value.VAL_CHANNEL {
			return value.NewNull()
		}
		chObj := args[0].Obj.(*value.ObjChannel)

		chObj.Lock.Lock()
		defer chObj.Lock.Unlock()

		if !chObj.Closed {
			close(chObj.Chan)
			chObj.Closed = true
		}
		return value.NewNull()
	})

	vm.DefineNative("chan_is_closed", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewBool(false)
		}
		if args[0].Type != value.VAL_CHANNEL {
			return value.NewBool(false)
		}
		chObj := args[0].Obj.(*value.ObjChannel)

		chObj.Lock.Lock()
		defer chObj.Lock.Unlock()

		return value.NewBool(chObj.Closed)
	})

	vm.DefineNative("chan_recv", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		if args[0].Type != value.VAL_CHANNEL {
			return value.NewNull()
		}
		ch := args[0].Obj.(*value.ObjChannel).Chan
		val, ok := <-ch
		if !ok {
			return value.NewNull()
		}
		return val
	})

	vm.DefineNative("make_wg", func(args []value.Value) value.Value {
		return value.NewWaitGroup()
	})

	vm.DefineNative("wg_add", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		if args[0].Type != value.VAL_WAITGROUP {
			return value.NewNull()
		}
		delta := int(0)
		if args[1].Type == value.VAL_INT {
			delta = int(args[1].AsInt)
		}
		if delta == 0 {
			return value.NewNull()
		}
		wg := args[0].Obj.(*value.ObjWaitGroup).Wg
		wg.Add(delta)
		return value.NewNull()
	})

	vm.DefineNative("wg_done", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		if args[0].Type != value.VAL_WAITGROUP {
			return value.NewNull()
		}
		wg := args[0].Obj.(*value.ObjWaitGroup).Wg
		wg.Done()
		return value.NewNull()
	})

	vm.DefineNative("wg_wait", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		if args[0].Type != value.VAL_WAITGROUP {
			return value.NewNull()
		}
		wg := args[0].Obj.(*value.ObjWaitGroup).Wg
		wg.Wait()
		return value.NewNull()
	})

	vm.DefineNative("to_str", func(args []value.Value) value.Value {
		if len(args) != 1 {
			// Should return error or empty?
			return value.NewString("")
		}
		if args[0].Type == value.VAL_BYTES {
			return value.NewString(args[0].Obj.(string))
		}
		return value.NewString(args[0].String())
	})
	vm.DefineNative("to_int", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewInt(0)
		}
		v := args[0]
		if v.Type == value.VAL_INT {
			return value.NewInt(v.AsInt)
		}
		if v.Type == value.VAL_FLOAT {
			return value.NewInt(int64(v.AsFloat))
		}
		if v.Type == value.VAL_OBJ {
			if s, ok := v.Obj.(string); ok {
				if i, err := strconv.ParseInt(s, 10, 64); err == nil {
					return value.NewInt(i)
				}
				if f, err := strconv.ParseFloat(s, 64); err == nil {
					return value.NewInt(int64(f))
				}
			}
		}
		return value.NewInt(0)
	})
	vm.DefineNative("to_float", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewFloat(0.0)
		}
		v := args[0]
		if v.Type == value.VAL_FLOAT {
			return value.NewFloat(v.AsFloat)
		}
		if v.Type == value.VAL_INT {
			return value.NewFloat(float64(v.AsInt))
		}
		if v.Type == value.VAL_OBJ {
			if s, ok := v.Obj.(string); ok {
				if f, err := strconv.ParseFloat(s, 64); err == nil {
					return value.NewFloat(f)
				}
			}
		}
		return value.NewFloat(0.0)
	})
	vm.DefineNative("time_now_ms", func(args []value.Value) value.Value {
		return value.NewInt(time.Now().UnixMilli())
	})
	vm.DefineNative("time_now", func(args []value.Value) value.Value {
		return value.NewInt(time.Now().Unix())
	})

	vm.DefineNative("time_sleep", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		ms := args[0].AsInt
		time.Sleep(time.Duration(ms) * time.Millisecond)
		return value.NewNull()
	})
	vm.DefineNative("time_now_datetime", func(args []value.Value) value.Value {
		// args[0] is DateTime struct def
		if len(args) < 1 {
			return value.NewNull()
		}
		structDef, ok := args[0].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		t := time.Now()
		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["year"] = value.NewInt(int64(t.Year()))
		inst.Fields["month"] = value.NewInt(int64(t.Month()))
		inst.Fields["day"] = value.NewInt(int64(t.Day()))
		inst.Fields["hour"] = value.NewInt(int64(t.Hour()))
		inst.Fields["minute"] = value.NewInt(int64(t.Minute()))
		inst.Fields["second"] = value.NewInt(int64(t.Second()))
		inst.Fields["weekday"] = value.NewInt(int64(t.Weekday()))
		inst.Fields["yearday"] = value.NewInt(int64(t.YearDay()))
		inst.Fields["timestamp"] = value.NewInt(t.Unix())

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("time_format", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewString("")
		}

		// Reconstruct time.Time from fields
		// Minimal fields: year, month, day, hour, minute, second
		y := int(inst.Fields["year"].AsInt)
		m := time.Month(inst.Fields["month"].AsInt)
		d := int(inst.Fields["day"].AsInt)
		h := int(inst.Fields["hour"].AsInt)
		min := int(inst.Fields["minute"].AsInt)
		s := int(inst.Fields["second"].AsInt)

		t := time.Date(y, m, d, h, min, s, 0, time.Local)
		return value.NewString(t.Format("2006-01-02 15:04:05"))
	})
	vm.DefineNative("time_format_date", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewString("")
		}
		y := int(inst.Fields["year"].AsInt)
		m := time.Month(inst.Fields["month"].AsInt)
		d := int(inst.Fields["day"].AsInt)
		t := time.Date(y, m, d, 0, 0, 0, 0, time.Local)
		return value.NewString(t.Format("2006-01-02"))
	})
	vm.DefineNative("time_format_time", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewString("")
		}
		h := int(inst.Fields["hour"].AsInt)
		min := int(inst.Fields["minute"].AsInt)
		s := int(inst.Fields["second"].AsInt)
		t := time.Date(0, 1, 1, h, min, s, 0, time.Local)
		return value.NewString(t.Format("15:04:05"))
	})
	vm.DefineNative("time_make_datetime", func(args []value.Value) value.Value {
		// args: structDef, y, m, d, h, min, s
		if len(args) < 7 {
			return value.NewNull()
		}
		structDef, ok := args[0].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		y := int(args[1].AsInt)
		m := time.Month(args[2].AsInt)
		d := int(args[3].AsInt)
		h := int(args[4].AsInt)
		min := int(args[5].AsInt)
		s := int(args[6].AsInt)

		t := time.Date(y, m, d, h, min, s, 0, time.Local)

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["year"] = value.NewInt(int64(t.Year()))
		inst.Fields["month"] = value.NewInt(int64(t.Month()))
		inst.Fields["day"] = value.NewInt(int64(t.Day()))
		inst.Fields["hour"] = value.NewInt(int64(t.Hour()))
		inst.Fields["minute"] = value.NewInt(int64(t.Minute()))
		inst.Fields["second"] = value.NewInt(int64(t.Second()))
		inst.Fields["weekday"] = value.NewInt(int64(t.Weekday()))
		inst.Fields["yearday"] = value.NewInt(int64(t.YearDay()))
		inst.Fields["timestamp"] = value.NewInt(t.Unix())

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("time_to_timestamp", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewInt(0)
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewInt(0)
		}

		val, ok := inst.Fields["timestamp"]
		if ok {
			return val
		}
		return value.NewInt(0)
	})
	vm.DefineNative("time_from_timestamp", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		ts := args[0].AsInt
		structDef, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		t := time.Unix(ts, 0)
		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["year"] = value.NewInt(int64(t.Year()))
		inst.Fields["month"] = value.NewInt(int64(t.Month()))
		inst.Fields["day"] = value.NewInt(int64(t.Day()))
		inst.Fields["hour"] = value.NewInt(int64(t.Hour()))
		inst.Fields["minute"] = value.NewInt(int64(t.Minute()))
		inst.Fields["second"] = value.NewInt(int64(t.Second()))
		inst.Fields["weekday"] = value.NewInt(int64(t.Weekday()))
		inst.Fields["yearday"] = value.NewInt(int64(t.YearDay()))
		inst.Fields["timestamp"] = value.NewInt(t.Unix())

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("time_diff", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewInt(0)
		}
		ts1 := args[0].AsInt
		ts2 := args[1].AsInt
		return value.NewInt(ts1 - ts2)
	})
	vm.DefineNative("time_add_days", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewInt(0)
		}
		ts := args[0].AsInt
		days := args[1].AsInt
		return value.NewInt(ts + (days * 86400))
	})
	vm.DefineNative("time_before", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewBool(false)
		}
		return value.NewBool(args[0].AsInt < args[1].AsInt)
	})
	vm.DefineNative("time_after", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewBool(false)
		}
		return value.NewBool(args[0].AsInt > args[1].AsInt)
	})
	vm.DefineNative("time_is_leap_year", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		year := args[0].AsInt
		return value.NewBool(year%4 == 0 && (year%100 != 0 || year%400 == 0))
	})
	vm.DefineNative("time_days_in_month", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewInt(0)
		}
		year := int(args[0].AsInt)
		month := time.Month(args[1].AsInt)
		// Trick: go to next month day 0
		t := time.Date(year, month+1, 0, 0, 0, 0, 0, time.UTC)
		return value.NewInt(int64(t.Day()))
	})
	vm.DefineNative("time_weekday_name", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		wd := time.Weekday(args[0].AsInt)

		names := []string{
			"Domingo", "Segunda-feira", "Terça-feira", "Quarta-feira",
			"Quinta-feira", "Sexta-feira", "Sábado",
		}
		if int(wd) >= 0 && int(wd) < len(names) {
			return value.NewString(names[wd])
		}
		return value.NewString(wd.String())
	})
	vm.DefineNative("time_month_name", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		m := time.Month(args[0].AsInt)
		names := map[time.Month]string{
			time.January: "Janeiro", time.February: "Fevereiro", time.March: "Março",
			time.April: "Abril", time.May: "Maio", time.June: "Junho",
			time.July: "Julho", time.August: "Agosto", time.September: "Setembro",
			time.October: "Outubro", time.November: "Novembro", time.December: "Dezembro",
		}
		if name, ok := names[m]; ok {
			return value.NewString(name)
		}
		return value.NewString(m.String())
	})
	vm.DefineNative("io_open", func(args []value.Value) value.Value {
		// args: path, mode, FileStructDef
		if len(args) < 3 {
			return value.NewNull()
		}
		path := args[0].String()
		mode := args[1].String()

		structDef, ok := args[2].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		flag := os.O_RDONLY
		if mode == "w" {
			flag = os.O_WRONLY | os.O_CREATE | os.O_TRUNC
		} else if mode == "a" {
			flag = os.O_WRONLY | os.O_CREATE | os.O_APPEND
		} else if mode == "rw" || mode == "r+" {
			flag = os.O_RDWR | os.O_CREATE
		}

		f, err := os.OpenFile(path, flag, 0644)
		isOpen := true
		var fd int64 = 0

		if err != nil {
			isOpen = false
		} else {
			fd = vm.nextFD
			vm.nextFD++
			vm.openFiles[fd] = f
		}

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["fd"] = value.NewInt(fd)
		inst.Fields["path"] = value.NewString(path)
		inst.Fields["mode"] = value.NewString(mode)
		inst.Fields["open"] = value.NewBool(isOpen)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("io_close", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewNull()
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}

		fd := inst.Fields["fd"].AsInt
		if f, exists := vm.openFiles[fd]; exists {
			f.Close()
			delete(vm.openFiles, fd)
			inst.Fields["open"] = value.NewBool(false)
		}
		return value.NewNull()
	})
	vm.DefineNative("io_write", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}

		fd := inst.Fields["fd"].AsInt
		if f, exists := vm.openFiles[fd]; exists {
			if args[1].Type == value.VAL_BYTES {
				// Bytes are stored as string in Obj, but treat as raw bytes
				data := args[1].Obj.(string)
				f.Write([]byte(data))
			} else {
				content := args[1].String()
				f.WriteString(content)
			}
		}
		return value.NewNull()
	})
	vm.DefineNative("io_read", func(args []value.Value) value.Value {
		// args: fileInst, IOResultStructDef
		if len(args) < 2 {
			return value.NewNull()
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resStruct, ok := args[1].Obj.(*value.ObjStruct) // IOResult
		if !ok {
			return value.NewNull()
		}

		fd := inst.Fields["fd"].AsInt
		var contentStr string
		var errorStr string
		var isOk bool = false

		if f, exists := vm.openFiles[fd]; exists {
			// Read all
			stat, _ := f.Stat()
			if stat.Size() > 0 {
				buf := make([]byte, stat.Size())
				f.Seek(0, 0)
				n, err := f.Read(buf)
				if err == nil || (err != nil && n > 0) { // simple read
					contentStr = string(buf[:n])
					isOk = true
				} else {
					errorStr = err.Error()
				}
			} else {
				isOk = true // empty file
			}
		} else {
			errorStr = "File not open"
		}

		resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
		resInst.Fields["ok"] = value.NewBool(isOk)
		resInst.Fields["data"] = value.NewString(contentStr)
		resInst.Fields["error"] = value.NewString(errorStr)
		return value.Value{Type: value.VAL_OBJ, Obj: resInst}
	})

	vm.DefineNative("io_read_bytes", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resStruct, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		fd := inst.Fields["fd"].AsInt
		var contentBytes []byte
		var errorStr string
		var isOk bool = false

		if f, exists := vm.openFiles[fd]; exists {
			// Read all
			stat, _ := f.Stat()
			if stat.Size() > 0 {
				buf := make([]byte, stat.Size())
				f.Seek(0, 0)
				n, err := f.Read(buf)
				if err == nil || (err != nil && n > 0) {
					contentBytes = buf[:n]
					isOk = true
				} else {
					errorStr = err.Error()
				}
			} else {
				contentBytes = []byte{}
				isOk = true
			}
		} else {
			errorStr = "File not open"
		}

		resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
		resInst.Fields["ok"] = value.NewBool(isOk)
		resInst.Fields["data"] = value.NewBytes(string(contentBytes))
		resInst.Fields["error"] = value.NewString(errorStr)
		return value.Value{Type: value.VAL_OBJ, Obj: resInst}
	})
	vm.DefineNative("io_exists", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		path := args[0].String()
		_, err := os.Stat(path)
		return value.NewBool(err == nil)
	})
	vm.DefineNative("io_remove", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		path := args[0].String()
		err := os.Remove(path)
		return value.NewBool(err == nil)
	})
	vm.DefineNative("io_read_lines", func(args []value.Value) value.Value {
		// args: fileInst, IOLinesResultStructDef
		if len(args) < 2 {
			return value.NewNull()
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resStruct, ok := args[1].Obj.(*value.ObjStruct) // IOLinesResult
		if !ok {
			return value.NewNull()
		}

		fd := inst.Fields["fd"].AsInt
		var lines []string
		var errorStr string
		var isOk bool = false

		if f, exists := vm.openFiles[fd]; exists {
			// Read all
			stat, _ := f.Stat()
			var contentStr string
			if stat.Size() > 0 {
				f.Seek(0, 0)
				buf := make([]byte, stat.Size())
				n, err := f.Read(buf)
				if err == nil || (err != nil && n > 0) {
					contentStr = string(buf[:n])
					isOk = true
				} else {
					errorStr = err.Error()
				}
			} else {
				isOk = true
			}

			if isOk {
				// Split by newlines, handling \r\n and \n
				// Naive split
				contentStr = strings.ReplaceAll(contentStr, "\r\n", "\n")
				lines = strings.Split(contentStr, "\n")
				// If last line is empty due to trailing newline, maybe keep it?
				// strings.Split("a\n", "\n") -> ["a", ""]
				// Usually read_lines might expect that. Let's keep it simple.
			}
		} else {
			errorStr = "File not open"
		}

		resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
		resInst.Fields["ok"] = value.NewBool(isOk)

		linesVal := make([]value.Value, len(lines))
		for i, line := range lines {
			linesVal[i] = value.NewString(line)
		}
		resInst.Fields["data"] = value.NewArray(linesVal)

		resInst.Fields["error"] = value.NewString(errorStr)
		return value.Value{Type: value.VAL_OBJ, Obj: resInst}
	})
	vm.DefineNative("io_stat", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		path := args[0].String()
		structDef, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		info, err := os.Stat(path)
		exists := (err == nil)
		size := int64(0)
		isDir := false
		if exists {
			size = info.Size()
			isDir = info.IsDir()
		}

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["exists"] = value.NewBool(exists)
		inst.Fields["size"] = value.NewInt(size)
		inst.Fields["is_dir"] = value.NewBool(isDir)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("io_mkdir", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		path := args[0].String()
		err := os.MkdirAll(path, 0755)
		return value.NewBool(err == nil)
	})

	vm.DefineNative("time_format_custom", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewString("")
		}
		inst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewString("")
		}
		fmtStr := args[1].Obj.(string)

		y := int(inst.Fields["year"].AsInt)
		m := time.Month(inst.Fields["month"].AsInt)
		d := int(inst.Fields["day"].AsInt)
		h := int(inst.Fields["hour"].AsInt)
		min := int(inst.Fields["minute"].AsInt)
		s := int(inst.Fields["second"].AsInt)
		// t := time.Date(y, m, d, h, min, s, 0, time.Local) // Unused in this simple implementation

		// Simplified replacement for strftime
		// Noxy: %Y=ano, %m=mês, %d=dia, %H=hora, %M=min, %S=seg
		res := fmtStr
		res = strings.ReplaceAll(res, "%Y", fmt.Sprintf("%04d", y))
		res = strings.ReplaceAll(res, "%m", fmt.Sprintf("%02d", m))
		res = strings.ReplaceAll(res, "%d", fmt.Sprintf("%02d", d))
		res = strings.ReplaceAll(res, "%H", fmt.Sprintf("%02d", h))
		res = strings.ReplaceAll(res, "%M", fmt.Sprintf("%02d", min))
		res = strings.ReplaceAll(res, "%S", fmt.Sprintf("%02d", s))

		return value.NewString(res)
	})
	vm.DefineNative("time_parse", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		str := args[0].Obj.(string)
		structDef, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		t, err := time.ParseInLocation("2006-01-02 15:04:05", str, time.Local)
		if err != nil {
			return value.NewNull()
		}

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["year"] = value.NewInt(int64(t.Year()))
		inst.Fields["month"] = value.NewInt(int64(t.Month()))
		inst.Fields["day"] = value.NewInt(int64(t.Day()))
		inst.Fields["hour"] = value.NewInt(int64(t.Hour()))
		inst.Fields["minute"] = value.NewInt(int64(t.Minute()))
		inst.Fields["second"] = value.NewInt(int64(t.Second()))
		inst.Fields["weekday"] = value.NewInt(int64(t.Weekday()))
		inst.Fields["yearday"] = value.NewInt(int64(t.YearDay()))
		inst.Fields["timestamp"] = value.NewInt(t.Unix())

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("time_parse_date", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		str := args[0].Obj.(string)
		structDef, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		t, err := time.ParseInLocation("2006-01-02", str, time.Local)
		if err != nil {
			return value.NewNull()
		}

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["year"] = value.NewInt(int64(t.Year()))
		inst.Fields["month"] = value.NewInt(int64(t.Month()))
		inst.Fields["day"] = value.NewInt(int64(t.Day()))
		inst.Fields["hour"] = value.NewInt(int64(t.Hour()))
		inst.Fields["minute"] = value.NewInt(int64(t.Minute()))
		inst.Fields["second"] = value.NewInt(int64(t.Second()))
		inst.Fields["weekday"] = value.NewInt(int64(t.Weekday()))
		inst.Fields["yearday"] = value.NewInt(int64(t.YearDay()))
		inst.Fields["timestamp"] = value.NewInt(t.Unix())

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("time_add_seconds", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewInt(0)
		}
		ts := args[0].AsInt
		secs := args[1].AsInt
		return value.NewInt(ts + secs)
	})
	vm.DefineNative("time_diff_duration", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewNull()
		}
		ts1 := args[0].AsInt
		ts2 := args[1].AsInt
		structDef, ok := args[2].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		diff := ts1 - ts2
		if diff < 0 {
			diff = -diff
		}

		totalSecs := ts1 - ts2
		absSecs := totalSecs
		if absSecs < 0 {
			absSecs = -absSecs
		}

		days := absSecs / 86400
		rem := absSecs % 86400
		hours := rem / 3600
		rem = rem % 3600
		mins := rem / 60
		secs := rem % 60

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["days"] = value.NewInt(days)
		inst.Fields["hours"] = value.NewInt(hours)
		inst.Fields["minutes"] = value.NewInt(mins)
		inst.Fields["seconds"] = value.NewInt(secs)
		inst.Fields["total_seconds"] = value.NewInt(totalSecs)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})

	// Strings Module
	vm.DefineNative("strings_contains", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewBool(false)
		}
		return value.NewBool(strings.Contains(args[0].String(), args[1].String()))
	})
	vm.DefineNative("strings_starts_with", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewBool(false)
		}
		return value.NewBool(strings.HasPrefix(args[0].String(), args[1].String()))
	})
	vm.DefineNative("strings_ends_with", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewBool(false)
		}
		return value.NewBool(strings.HasSuffix(args[0].String(), args[1].String()))
	})
	vm.DefineNative("strings_index_of", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewInt(-1)
		}
		return value.NewInt(int64(strings.Index(args[0].String(), args[1].String())))
	})
	vm.DefineNative("strings_count", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewInt(0)
		}
		return value.NewInt(int64(strings.Count(args[0].String(), args[1].String())))
	})
	vm.DefineNative("strings_to_upper", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		return value.NewString(strings.ToUpper(args[0].String()))
	})
	vm.DefineNative("strings_to_lower", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		return value.NewString(strings.ToLower(args[0].String()))
	})
	vm.DefineNative("strings_trim", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		return value.NewString(strings.TrimSpace(args[0].String()))
	})

	// Input
	vm.DefineNative("input", func(args []value.Value) value.Value {
		// args[0]: prompt (optional)
		if len(args) > 0 {
			fmt.Print(args[0].String())
		}
		reader := bufio.NewReader(os.Stdin)
		text, _ := reader.ReadString('\n')
		// Trim newline (windows \r\n and unix \n)
		text = strings.TrimRight(text, "\r\n")
		return value.NewString(text)
	})
	vm.DefineNative("strings_reverse", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		s := args[0].String()
		runes := []rune(s)
		for i, j := 0, len(runes)-1; i < j; i, j = i+1, j-1 {
			runes[i], runes[j] = runes[j], runes[i]
		}
		return value.NewString(string(runes))
	})
	vm.DefineNative("strings_repeat", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewString("")
		}
		return value.NewString(strings.Repeat(args[0].String(), int(args[1].AsInt)))
	})
	vm.DefineNative("strings_substring", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewString("")
		}
		s := args[0].String()
		start := int(args[1].AsInt)
		end := int(args[2].AsInt)
		if start < 0 {
			start = 0
		}
		if end > len(s) {
			end = len(s)
		}
		if start > end {
			return value.NewString("")
		}
		return value.NewString(s[start:end])
	})
	vm.DefineNative("strings_replace", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewString("")
		}
		return value.NewString(strings.ReplaceAll(args[0].String(), args[1].String(), args[2].String()))
	})
	vm.DefineNative("strings_replace_first", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewString("")
		}
		return value.NewString(strings.Replace(args[0].String(), args[1].String(), args[2].String(), 1))
	})
	vm.DefineNative("strings_pad_left", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewString("")
		}
		s := args[0].String()
		totalLen := int(args[1].AsInt)
		padChar := args[2].String()
		if len(s) >= totalLen {
			return value.NewString(s)
		}
		padding := totalLen - len(s)
		return value.NewString(strings.Repeat(padChar, padding) + s)
	})
	vm.DefineNative("strings_split", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewNull()
		}
		s := args[0].String()
		sep := args[1].String()
		structDef, ok := args[2].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		parts := strings.Split(s, sep)

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["count"] = value.NewInt(int64(len(parts)))

		partValues := make([]value.Value, len(parts))
		for i, p := range parts {
			partValues[i] = value.NewString(p)
		}
		inst.Fields["parts"] = value.NewArray(partValues)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})
	vm.DefineNative("strings_join_count", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewString("")
		}
		arrVal := args[0]
		sep := args[1].String()
		count := int(args[2].AsInt)

		if arrVal.Type == value.VAL_OBJ {
			if arr, ok := arrVal.Obj.(*value.ObjArray); ok {
				var parts []string
				max := len(arr.Elements)
				if count < max {
					max = count
				}
				for i := 0; i < max; i++ {
					parts = append(parts, arr.Elements[i].String())
				}
				return value.NewString(strings.Join(parts, sep))
			}
		}
		return value.NewString("")
	})
	vm.DefineNative("ord", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewInt(0)
		}
		s := args[0].String()
		if len(s) == 0 {
			return value.NewInt(0)
		}
		return value.NewInt(int64(s[0]))
	})
	vm.DefineNative("strings_contains", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewBool(false)
		}
		s := args[0].String()
		substr := args[1].String()
		return value.NewBool(strings.Contains(s, substr))
	})
	vm.DefineNative("strings_replace", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewString("")
		}
		s := args[0].String()
		old := args[1].String()
		new := args[2].String()
		return value.NewString(strings.ReplaceAll(s, old, new))
	})
	vm.DefineNative("strings_substring", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewString("")
		}
		s := args[0].String()
		start := int(args[1].AsInt)
		end := int(args[2].AsInt)

		if start < 0 {
			start = 0
		}
		if end > len(s) {
			end = len(s)
		}
		if start >= end {
			return value.NewString("")
		}

		return value.NewString(s[start:end])
	})
	vm.DefineNative("strings_is_empty", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(true)
		}
		return value.NewBool(len(args[0].String()) == 0)
	})
	vm.DefineNative("strings_is_digit", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		s := args[0].String()
		if len(s) == 0 {
			return value.NewBool(false)
		}
		for _, r := range s {
			if r < '0' || r > '9' {
				return value.NewBool(false)
			}
		}
		return value.NewBool(true)
	})
	vm.DefineNative("strings_is_alpha", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		s := args[0].String()
		if len(s) == 0 {
			return value.NewBool(false)
		}
		for _, r := range s {
			if (r < 'a' || r > 'z') && (r < 'A' || r > 'Z') {
				return value.NewBool(false)
			}
		}
		return value.NewBool(true)
	})
	vm.DefineNative("strings_is_alnum", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		s := args[0].String()
		if len(s) == 0 {
			return value.NewBool(false)
		}
		for _, r := range s {
			isDigit := r >= '0' && r <= '9'
			isAlpha := (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z')
			if !isDigit && !isAlpha {
				return value.NewBool(false)
			}
		}
		return value.NewBool(true)
	})
	vm.DefineNative("strings_is_space", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewBool(false)
		}
		s := args[0].String()
		if len(s) == 0 {
			return value.NewBool(false)
		}
		for _, r := range s {
			if r != ' ' && r != '\t' && r != '\n' && r != '\r' {
				return value.NewBool(false)
			}
		}
		return value.NewBool(true)
	})
	vm.DefineNative("strings_char_at", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewString("")
		}
		s := args[0].String()
		idx := int(args[1].AsInt)
		if idx < 0 || idx >= len(s) {
			return value.NewString("")
		}
		return value.NewString(string(s[idx]))
	})
	vm.DefineNative("strings_from_char_code", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		return value.NewString(string(rune(args[0].AsInt)))
	})

	// Sys Module
	vm.DefineNative("sys_os", func(args []value.Value) value.Value {
		return value.NewString(runtime.GOOS)
	})

	vm.DefineNative("sys_exec", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		cmdStr := args[0].String()
		structDef, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		var cmd *exec.Cmd
		if os.PathSeparator == '\\' {
			cmd = exec.Command("cmd", "/C", cmdStr)
		} else {
			cmd = exec.Command("sh", "-c", cmdStr)
		}

		cmd.Stdout = os.Stdout
		cmd.Stderr = os.Stderr

		err := cmd.Run()
		exitCode := 0
		okVal := true

		var outputStr string = "" // No captured output for sys_exec

		if err != nil {
			okVal = false
			if exitErr, ok := err.(*exec.ExitError); ok {
				exitCode = exitErr.ExitCode()
			} else {
				exitCode = 1
			}
		}

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["exit_code"] = value.NewInt(int64(exitCode))
		inst.Fields["output"] = value.NewString(outputStr)
		inst.Fields["ok"] = value.NewBool(okVal)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})

	vm.DefineNative("sys_exec_output", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		cmdStr := args[0].String()
		structDef, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		var cmd *exec.Cmd
		if os.PathSeparator == '\\' {
			cmd = exec.Command("cmd", "/C", cmdStr)
		} else {
			cmd = exec.Command("sh", "-c", cmdStr)
		}

		outBytes, err := cmd.CombinedOutput()
		outputStr := string(outBytes)

		exitCode := 0
		okVal := true // Logic: if exit code 0 also? or just ran? usually ok implies success.

		if err != nil {
			if exitErr, ok := err.(*exec.ExitError); ok {
				exitCode = exitErr.ExitCode()
			} else {
				exitCode = 1
			}
			okVal = false
		} else {
			// On success err is nil
			okVal = true
		}

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["exit_code"] = value.NewInt(int64(exitCode))
		inst.Fields["output"] = value.NewString(strings.TrimSpace(outputStr))
		inst.Fields["ok"] = value.NewBool(okVal)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})

	vm.DefineNative("sys_getenv", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		key := args[0].String()
		structDef, ok := args[1].Obj.(*value.ObjStruct)
		if !ok {
			return value.NewNull()
		}

		val, found := os.LookupEnv(key)

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["value"] = value.NewString(val)
		inst.Fields["ok"] = value.NewBool(found)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})

	vm.DefineNative("sys_setenv", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewBool(false)
		}
		key := args[0].String()
		val := args[1].String()
		err := os.Setenv(key, val)
		return value.NewBool(err == nil)
	})

	vm.DefineNative("sys_getcwd", func(args []value.Value) value.Value {
		dir, err := os.Getwd()
		if err != nil {
			return value.NewString("")
		}
		return value.NewString(dir)
	})

	vm.DefineNative("sys_argv", func(args []value.Value) value.Value {
		// Convert os.Args to string[]
		vals := make([]value.Value, len(os.Args))
		for i, a := range os.Args {
			vals[i] = value.NewString(a)
		}
		return value.NewArray(vals)
	})

	vm.DefineNative("sys_sleep", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewNull()
		}
		ms := args[0].AsInt
		time.Sleep(time.Duration(ms) * time.Millisecond)
		return value.NewNull()
	})

	vm.DefineNative("sys_exit", func(args []value.Value) value.Value {
		code := 0
		if len(args) > 0 {
			code = int(args[0].AsInt)
		}
		os.Exit(code)
		return value.NewNull()
	})

	vm.DefineNative("length", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewInt(0)
		}
		arg := args[0]
		if arg.Type == value.VAL_BYTES {
			if str, ok := arg.Obj.(string); ok {
				return value.NewInt(int64(len(str)))
			}
		}
		if arg.Type == value.VAL_OBJ {
			if str, ok := arg.Obj.(string); ok {
				return value.NewInt(int64(len(str)))
			}
			if arr, ok := arg.Obj.(*value.ObjArray); ok {
				return value.NewInt(int64(len(arr.Elements)))
			}
			if mp, ok := arg.Obj.(*value.ObjMap); ok {
				return value.NewInt(int64(len(mp.Data)))
			}
		}
		return value.NewInt(0)
	})

	vm.DefineNative("keys", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewArray(nil)
		}
		mapVal := args[0]
		if mapVal.Type == value.VAL_OBJ {
			if m, ok := mapVal.Obj.(*value.ObjMap); ok {
				keys := make([]value.Value, 0, len(m.Data))
				for k := range m.Data {
					if kInt, ok := k.(int64); ok {
						keys = append(keys, value.NewInt(kInt))
					} else if kStr, ok := k.(string); ok {
						keys = append(keys, value.NewString(kStr))
					}
				}
				return value.NewArray(keys)
			}
		}
		return value.NewArray(nil)
	})

	vm.DefineNative("delete", func(args []value.Value) value.Value {
		if len(args) != 2 {
			return value.NewNull()
		}
		mapVal := args[0]
		keyVal := args[1]
		if mapVal.Type == value.VAL_OBJ {
			if m, ok := mapVal.Obj.(*value.ObjMap); ok {
				var key interface{}
				if keyVal.Type == value.VAL_INT {
					key = keyVal.AsInt
				} else if keyVal.Type == value.VAL_OBJ {
					if str, ok := keyVal.Obj.(string); ok {
						key = str
					}
				}
				if key != nil {
					delete(m.Data, key)
				}
			}
		}
		return value.NewNull()
	})
	vm.DefineNative("append", func(args []value.Value) value.Value {
		if len(args) != 2 {
			return value.NewNull()
		}
		arrVal := args[0]
		item := args[1]
		if arrVal.Type == value.VAL_OBJ {
			if arr, ok := arrVal.Obj.(*value.ObjArray); ok {
				arr.Elements = append(arr.Elements, item)
			}
		}
		return value.NewNull()
	})
	vm.DefineNative("pop", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		arrVal := args[0]
		if arrVal.Type == value.VAL_OBJ {
			if arr, ok := arrVal.Obj.(*value.ObjArray); ok {
				if len(arr.Elements) == 0 {
					return value.NewNull()
				}
				val := arr.Elements[len(arr.Elements)-1]
				arr.Elements = arr.Elements[:len(arr.Elements)-1]
				return val
			}
		}
		return value.NewNull()
	})
	vm.DefineNative("slice", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewNull()
		}
		seq := args[0]
		start := int(args[1].AsInt)
		end := int(args[2].AsInt)

		// Clamp logic helper
		clamp := func(idx, length int) int {
			if idx < 0 {
				return 0
			}
			if idx > length {
				return length
			}
			return idx
		}

		switch seq.Type {
		case value.VAL_OBJ:
			if str, ok := seq.Obj.(string); ok {
				runes := []rune(str)
				start = clamp(start, len(runes))
				end = clamp(end, len(runes))
				if start > end {
					return value.NewString("")
				}
				return value.NewString(string(runes[start:end]))
			}
			if arr, ok := seq.Obj.(*value.ObjArray); ok {
				start = clamp(start, len(arr.Elements))
				end = clamp(end, len(arr.Elements))
				if start > end {
					return value.NewArray(nil)
				}

				newElems := make([]value.Value, end-start)
				copy(newElems, arr.Elements[start:end])
				return value.NewArray(newElems)
			}
		case value.VAL_BYTES:
			if str, ok := seq.Obj.(string); ok {
				// Bytes stored as string
				start = clamp(start, len(str))
				end = clamp(end, len(str))
				if start > end {
					return value.NewBytes("")
				}
				return value.NewBytes(str[start:end])
			}
		}
		return value.NewNull()
	})
	vm.DefineNative("contains", func(args []value.Value) value.Value {
		if len(args) != 2 {
			return value.NewBool(false)
		}
		arrVal := args[0]
		target := args[1]
		if arrVal.Type == value.VAL_OBJ {
			if arr, ok := arrVal.Obj.(*value.ObjArray); ok {
				for _, el := range arr.Elements {
					if valuesEqual(el, target) {
						return value.NewBool(true)
					}
				}
			}
		}
		return value.NewBool(false)
	})
	vm.DefineNative("has_key", func(args []value.Value) value.Value {
		if len(args) != 2 {
			return value.NewBool(false)
		}
		mapVal := args[0]
		keyVal := args[1]
		if mapVal.Type == value.VAL_OBJ {
			if mapObj, ok := mapVal.Obj.(*value.ObjMap); ok {
				var key interface{}
				if keyVal.Type == value.VAL_INT {
					key = keyVal.AsInt
				} else if keyVal.Type == value.VAL_OBJ {
					if str, ok := keyVal.Obj.(string); ok {
						key = str
					} else {
						return value.NewBool(false)
					}
				} else {
					return value.NewBool(false)
				}
				_, ok := mapObj.Data[key]
				return value.NewBool(ok)
			}
		}
		return value.NewBool(false)
	})
	vm.DefineNative("to_bytes", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewBytes("")
		}
		arg := args[0]
		switch arg.Type {
		case value.VAL_OBJ:
			if str, ok := arg.Obj.(string); ok {
				return value.NewBytes(str)
			}
			if arr, ok := arg.Obj.(*value.ObjArray); ok {
				// Array of ints -> bytes
				bs := make([]byte, len(arr.Elements))
				for i, el := range arr.Elements {
					if el.Type == value.VAL_INT {
						bs[i] = byte(el.AsInt)
					}
				}
				return value.NewBytes(string(bs))
			}
		case value.VAL_INT:
			// Single int to single byte
			return value.NewBytes(string([]byte{byte(arg.AsInt)}))
		}
		return value.NewBytes("")
	})

	// Net Native Functions
	vm.DefineNative("net_listen", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		host := args[0].String()
		port := int(args[1].AsInt)
		addr := fmt.Sprintf("%s:%d", host, port)

		listener, err := net.Listen("tcp", addr)
		if err != nil {
			// Return Socket with open=false
			socketFields := map[string]value.Value{
				"fd":   value.NewInt(-1),
				"addr": value.NewString(host),
				"port": value.NewInt(int64(port)),
				"open": value.NewBool(false),
			}
			return value.NewMapWithData(socketFields)
		}

		vm.shared.NetLock.Lock()
		id := vm.shared.NextNetID
		vm.shared.NextNetID++
		vm.shared.NetListeners[id] = listener
		vm.shared.NetLock.Unlock()

		socketFields := map[string]value.Value{
			"fd":   value.NewInt(int64(id)),
			"addr": value.NewString(host),
			"port": value.NewInt(int64(port)),
			"open": value.NewBool(true),
		}
		return value.NewMapWithData(socketFields)
	})

	vm.DefineNative("net_accept", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewNull()
		}
		sockMap, ok := args[0].Obj.(*value.ObjMap)
		if !ok {
			return value.NewNull()
		}
		fdVal, exists := sockMap.Data["fd"]
		if !exists {
			return value.NewNull()
		}
		fd := int(fdVal.AsInt)

		vm.shared.NetLock.Lock()
		listener, ok := vm.shared.NetListeners[fd]
		vm.shared.NetLock.Unlock()

		if !ok {
			socketFields := map[string]value.Value{
				"fd":   value.NewInt(-1),
				"addr": value.NewString(""),
				"port": value.NewInt(0),
				"open": value.NewBool(false),
			}
			return value.NewMapWithData(socketFields)
		}

		// Check buffered connection from select
		var conn net.Conn
		var err error

		if bufferedConn, ok := vm.netBufferedConns[fd]; ok {
			conn = bufferedConn
			delete(vm.netBufferedConns, fd)
		} else {
			// Accept blocks. We should UNLOCK before accepting?
			// Yes, we unlocked above.
			conn, err = listener.Accept()
		}

		if err != nil {
			socketFields := map[string]value.Value{
				"fd":   value.NewInt(-1),
				"addr": value.NewString(""),
				"port": value.NewInt(0),
				"open": value.NewBool(false),
			}
			return value.NewMapWithData(socketFields)
		}

		vm.shared.NetLock.Lock()
		id := vm.shared.NextNetID
		vm.shared.NextNetID++
		vm.shared.NetConns[id] = conn
		vm.shared.NetLock.Unlock()

		remoteAddr := conn.RemoteAddr().String()
		socketFields := map[string]value.Value{
			"fd":   value.NewInt(int64(id)),
			"addr": value.NewString(remoteAddr),
			"port": value.NewInt(0),
			"open": value.NewBool(true),
		}
		return value.NewMapWithData(socketFields)
	})

	vm.DefineNative("net_connect", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		host := args[0].String()
		port := int(args[1].AsInt)
		addr := fmt.Sprintf("%s:%d", host, port)

		conn, err := net.DialTimeout("tcp", addr, 5*time.Second)
		if err != nil {
			socketFields := map[string]value.Value{
				"fd":   value.NewInt(-1),
				"addr": value.NewString(host),
				"port": value.NewInt(int64(port)),
				"open": value.NewBool(false),
			}
			return value.NewMapWithData(socketFields)
		}

		vm.shared.NetLock.Lock()
		id := vm.shared.NextNetID
		vm.shared.NextNetID++
		vm.shared.NetConns[id] = conn
		vm.shared.NetLock.Unlock()

		socketFields := map[string]value.Value{
			"fd":   value.NewInt(int64(id)),
			"addr": value.NewString(host),
			"port": value.NewInt(int64(port)),
			"open": value.NewBool(true),
		}
		return value.NewMapWithData(socketFields)
	})

	vm.DefineNative("net_recv", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		sockMap, ok := args[0].Obj.(*value.ObjMap)
		if !ok {
			return value.NewNull()
		}
		fdVal, _ := sockMap.Data["fd"]
		fd := int(fdVal.AsInt)
		size := int(args[1].AsInt)

		vm.shared.NetLock.Lock()
		conn, ok := vm.shared.NetConns[fd]
		vm.shared.NetLock.Unlock()

		if !ok {
			resultFields := map[string]value.Value{
				"ok":    value.NewBool(false),
				"data":  value.NewBytes(""),
				"count": value.NewInt(0),
				"error": value.NewString("invalid socket"),
			}
			return value.NewMapWithData(resultFields)
		}

		var n int
		buf := make([]byte, size)

		// Check buffered data from select
		if buffered, ok := vm.netBufferedData[fd]; ok {
			// Copy buffered data
			copy(buf, buffered)
			n = len(buffered)
			delete(vm.netBufferedData, fd)
		}

		// Try to read more if space available
		if n < size {
			// Blocking read (no deadline)
			n2, err2 := conn.Read(buf[n:])
			if n2 > 0 {
				n += n2
			}

			// Ignore timeout errors if we have at least some data
			if err2 != nil {
				if n == 0 {
					// Only return error if we really got nothing
					if err2 != nil && n2 == 0 {
						if err2 == io.EOF {
							// Return ok=true, count=0 for EOF
							resultFields := map[string]value.Value{
								"ok":    value.NewBool(true),
								"data":  value.NewBytes(""),
								"count": value.NewInt(0),
								"error": value.NewString(""),
							}
							return value.NewMapWithData(resultFields)
						}
						resultFields := map[string]value.Value{
							"ok":    value.NewBool(false),
							"data":  value.NewBytes(""),
							"count": value.NewInt(0),
							"error": value.NewString(err2.Error()),
						}
						return value.NewMapWithData(resultFields)
					}
				}
			}
		}

		resultFields := map[string]value.Value{
			"ok":    value.NewBool(true),
			"data":  value.NewBytes(string(buf[:n])),
			"count": value.NewInt(int64(n)),
			"error": value.NewString(""),
		}
		return value.NewMapWithData(resultFields)
	})

	vm.DefineNative("net_send", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		sockMap, ok := args[0].Obj.(*value.ObjMap)
		if !ok {
			fmt.Printf("DEBUG: net_send args[0] not map: %T %v\n", args[0].Obj, args[0].Obj)
			return value.NewNull()
		}
		fdVal, _ := sockMap.Data["fd"]
		fd := int(fdVal.AsInt)
		var data string
		if args[1].Type == value.VAL_BYTES {
			data = args[1].Obj.(string)
		} else {
			data = args[1].String()
		}

		vm.shared.NetLock.Lock()
		conn, ok := vm.shared.NetConns[fd]
		vm.shared.NetLock.Unlock()

		if !ok {
			resultFields := map[string]value.Value{
				"ok":    value.NewBool(false),
				"data":  value.NewBytes(""),
				"count": value.NewInt(0),
				"error": value.NewString("invalid socket"),
			}
			return value.NewMapWithData(resultFields)
		}

		n, err := conn.Write([]byte(data))
		if err != nil {
			resultFields := map[string]value.Value{
				"ok":    value.NewBool(false),
				"data":  value.NewBytes(""),
				"count": value.NewInt(0),
				"error": value.NewString(err.Error()),
			}
			return value.NewMapWithData(resultFields)
		}

		resultFields := map[string]value.Value{
			"ok":    value.NewBool(true),
			"data":  value.NewBytes(""),
			"count": value.NewInt(int64(n)),
			"error": value.NewString(""),
		}
		return value.NewMapWithData(resultFields)
	})

	vm.DefineNative("net_close", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewNull()
		}

		var fd int
		// Check if arg is int (new style) or map (old style compatibility if needed, but we changed net.nx)
		if args[0].Type == value.VAL_INT {
			fd = int(args[0].AsInt)
		} else if args[0].Type == value.VAL_OBJ {
			// Fallback for old calls? Or just error.
			if sockMap, ok := args[0].Obj.(*value.ObjMap); ok {
				if fdVal, found := sockMap.Data["fd"]; found {
					fd = int(fdVal.AsInt)
				}
			}
		} else {
			return value.NewNull()
		}

		vm.shared.NetLock.Lock()
		defer vm.shared.NetLock.Unlock()

		// Try closing as listener
		if listener, ok := vm.shared.NetListeners[fd]; ok {
			listener.Close()
			delete(vm.shared.NetListeners, fd)
			return value.NewNull()
		}

		// Try closing as connection
		if conn, ok := vm.shared.NetConns[fd]; ok {
			conn.Close()
			delete(vm.shared.NetConns, fd)
		}

		return value.NewNull()
	})

	vm.DefineNative("net_setblocking", func(args []value.Value) value.Value {
		// For TCP in Go, blocking is handled at a different level
		// This is a no-op for now, as Go handles timeouts via SetDeadline
		return value.NewNull()
	})

	vm.DefineNative("net_select", func(args []value.Value) value.Value {
		// args: read, write (ignored), err (ignored), timeout
		if len(args) < 4 {
			return value.NewNull() // Or error map
		}

		timeoutMs := int(args[3].AsInt)
		// Minimum 1ms to allow polling
		if timeoutMs < 1 {
			timeoutMs = 1
		}

		// Prepare Result Data
		readyRead := make([]value.Value, 0)

		// Parse Read Set
		readArrVal := args[0]
		if readArrVal.Type == value.VAL_OBJ {
			if arr, ok := readArrVal.Obj.(*value.ObjArray); ok {
				for _, el := range arr.Elements {
					if el.Type == value.VAL_OBJ { // Check if socket (Map or Instance)
						// Extract FD
						var fd int64 = -1

						if m, ok := el.Obj.(*value.ObjMap); ok {
							if f, ok := m.Data["fd"]; ok {
								fd = f.AsInt
							}
						} else if inst, ok := el.Obj.(*value.ObjInstance); ok {
							if f, ok := inst.Fields["fd"]; ok {
								fd = f.AsInt
							}
						}

						if fd != -1 {
							isReady := false
							id := int(fd)

							// 1. Check buffers first
							if _, ok := vm.netBufferedConns[id]; ok {
								isReady = true
							} else if _, ok := vm.netBufferedData[id]; ok {
								isReady = true
							} else {
								// 2. Poll
								vm.shared.NetLock.Lock()
								l, isListener := vm.shared.NetListeners[id]
								c, isConn := vm.shared.NetConns[id]
								vm.shared.NetLock.Unlock()

								if isListener {
									if tcpL, ok := l.(*net.TCPListener); ok {
										tcpL.SetDeadline(time.Now().Add(time.Millisecond * time.Duration(timeoutMs)))
										conn, err := l.Accept()
										if err == nil {
											isReady = true
											vm.netBufferedConns[id] = conn
										}
										// Reset deadline?
										tcpL.SetDeadline(time.Time{})
									}
								} else if isConn {
									conn := c
									conn.SetReadDeadline(time.Now().Add(time.Millisecond * time.Duration(timeoutMs)))
									buf := make([]byte, 1) // Peek 1 byte
									n, err := conn.Read(buf)
									if err == nil && n > 0 {
										isReady = true
										// Buffer the data
										vm.netBufferedData[id] = buf[:n]
									}
									// Reset deadline
									conn.SetReadDeadline(time.Time{})
								}
							}

							if isReady {
								readyRead = append(readyRead, el)
							}
						}
					}
				}
			}
		}

		// Construct SelectResult Map
		// struct SelectResult { read: Socket[64], read_count: int, ... }

		// Fill read array up to 64
		resReadArr := make([]value.Value, 64)
		for i := 0; i < 64; i++ {
			if i < len(readyRead) {
				resReadArr[i] = readyRead[i]
			} else {
				resReadArr[i] = value.NewNull()
			}
		}

		// Empties for others
		emptyArr := make([]value.Value, 64)
		for i := 0; i < 64; i++ {
			emptyArr[i] = value.NewNull()
		}

		resFields := map[string]value.Value{
			"read":        value.NewArray(resReadArr),
			"read_count":  value.NewInt(int64(len(readyRead))),
			"write":       value.NewArray(emptyArr),
			"write_count": value.NewInt(0),
			"error":       value.NewArray(emptyArr),
			"error_count": value.NewInt(0),
		}
		return value.NewMapWithData(resFields)
	})

	// SQLite Native Functions
	vm.DefineNative("sqlite_open", func(args []value.Value) value.Value {
		if len(args) != 2 {
			return value.NewNull()
		} // path, wrapper struct
		path := args[0].String()
		structInst, ok := args[1].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		structDef := structInst.Struct

		db, err := sql.Open("sqlite", path)
		openVal := true
		if err != nil {
			openVal = false
		} else {
			if err = db.Ping(); err != nil {
				openVal = false
			}
		}

		vm.shared.DbLock.Lock()
		id := vm.shared.NextDbID
		vm.shared.NextDbID++
		vm.shared.DbHandles[id] = db
		vm.shared.DbLock.Unlock()

		inst := value.NewInstance(structDef).Obj.(*value.ObjInstance)
		inst.Fields["handle"] = value.NewInt(int64(id))
		inst.Fields["open"] = value.NewBool(openVal)

		return value.Value{Type: value.VAL_OBJ, Obj: inst}
	})

	vm.DefineNative("sqlite_close", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		dbInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}

		handle := int(dbInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		defer vm.shared.DbLock.Unlock()

		if db, ok := vm.shared.DbHandles[handle]; ok {
			db.Close()
			delete(vm.shared.DbHandles, handle)
			dbInst.Fields["open"] = value.NewBool(false)
		}
		return value.NewNull()
	})

	vm.DefineNative("sqlite_exec", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewNull()
		}
		dbInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		sqlStr := args[1].String()

		resTmplInst, ok := args[2].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resStruct := resTmplInst.Struct

		handle := int(dbInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		db, ok := vm.shared.DbHandles[handle]
		vm.shared.DbLock.Unlock() // Unlock for Exec

		if ok {
			result, err := db.Exec(sqlStr)
			resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
			if err != nil {
				resInst.Fields["ok"] = value.NewBool(false)
				resInst.Fields["error"] = value.NewString(err.Error())
				resInst.Fields["rows_affected"] = value.NewInt(0)
				resInst.Fields["last_insert_id"] = value.NewInt(0)
			} else {
				rowsAffected, _ := result.RowsAffected()
				lastId, _ := result.LastInsertId()
				resInst.Fields["ok"] = value.NewBool(true)
				resInst.Fields["error"] = value.NewString("")
				resInst.Fields["rows_affected"] = value.NewInt(rowsAffected)
				resInst.Fields["last_insert_id"] = value.NewInt(lastId)
			}
			return value.Value{Type: value.VAL_OBJ, Obj: resInst}
		}
		// Invalid handle
		resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
		resInst.Fields["ok"] = value.NewBool(false)
		resInst.Fields["error"] = value.NewString("invalid database handle")
		resInst.Fields["rows_affected"] = value.NewInt(0)
		resInst.Fields["last_insert_id"] = value.NewInt(0)
		return value.Value{Type: value.VAL_OBJ, Obj: resInst}
	})

	vm.DefineNative("sqlite_exec_params", func(args []value.Value) value.Value {
		if len(args) < 4 {
			return value.NewNull()
		}
		dbInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		sqlStr := args[1].String()
		paramsArray, ok := args[2].Obj.(*value.ObjArray)
		if !ok {
			return value.NewNull()
		}

		resTmplInst, ok := args[3].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resStruct := resTmplInst.Struct

		handle := int(dbInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		db, ok := vm.shared.DbHandles[handle]
		vm.shared.DbLock.Unlock()

		if ok {
			// Convert params
			queryArgs := make([]interface{}, len(paramsArray.Elements))
			for i, val := range paramsArray.Elements {
				switch val.Type {
				case value.VAL_INT:
					queryArgs[i] = val.AsInt
				case value.VAL_FLOAT:
					queryArgs[i] = val.AsFloat
				case value.VAL_BOOL:
					queryArgs[i] = val.AsBool
				case value.VAL_NULL:
					queryArgs[i] = nil
				case value.VAL_OBJ:
					if b, ok := val.Obj.(string); ok {
						queryArgs[i] = b
					} else {
						queryArgs[i] = val.String()
					}
				default:
					queryArgs[i] = val.String()
				}
			}

			result, err := db.Exec(sqlStr, queryArgs...)
			resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
			if err != nil {
				resInst.Fields["ok"] = value.NewBool(false)
				resInst.Fields["error"] = value.NewString(err.Error())
				resInst.Fields["rows_affected"] = value.NewInt(0)
				resInst.Fields["last_insert_id"] = value.NewInt(0)
			} else {
				rowsAffected, _ := result.RowsAffected()
				lastId, _ := result.LastInsertId()
				resInst.Fields["ok"] = value.NewBool(true)
				resInst.Fields["error"] = value.NewString("")
				resInst.Fields["rows_affected"] = value.NewInt(rowsAffected)
				resInst.Fields["last_insert_id"] = value.NewInt(lastId)
			}
			return value.Value{Type: value.VAL_OBJ, Obj: resInst}
		}
		// Invalid handle
		resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
		resInst.Fields["ok"] = value.NewBool(false)
		resInst.Fields["error"] = value.NewString("invalid database handle")
		resInst.Fields["rows_affected"] = value.NewInt(0)
		resInst.Fields["last_insert_id"] = value.NewInt(0)
		return value.Value{Type: value.VAL_OBJ, Obj: resInst}
	})

	vm.DefineNative("sqlite_prepare", func(args []value.Value) value.Value {
		if len(args) < 3 {
			return value.NewNull()
		} // db, sql, stmt wrapper
		dbInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		sqlStr := args[1].String()
		stmtInst, ok := args[2].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		stmtStructDef := stmtInst.Struct

		handle := int(dbInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		db, ok := vm.shared.DbHandles[handle]
		vm.shared.DbLock.Unlock()

		if ok {
			stmt, err := db.Prepare(sqlStr)
			if err == nil {
				vm.shared.DbLock.Lock()
				id := vm.shared.NextStmtID
				vm.shared.NextStmtID++
				vm.shared.StmtHandles[id] = stmt
				vm.shared.StmtParams[id] = make(map[int]interface{})
				vm.shared.DbLock.Unlock()

				inst := value.NewInstance(stmtStructDef).Obj.(*value.ObjInstance)
				inst.Fields["handle"] = value.NewInt(int64(id))
				return value.Value{Type: value.VAL_OBJ, Obj: inst}
			}
		}
		return value.NewNull()
	})

	bindFunc := func(args []value.Value, val interface{}) value.Value {
		if len(args) < 3 {
			return value.NewNull()
		}
		stmtInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		idx := int(args[1].AsInt)

		handle := int(stmtInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		defer vm.shared.DbLock.Unlock()

		if _, ok := vm.shared.StmtHandles[handle]; ok {
			if vm.shared.StmtParams[handle] == nil {
				vm.shared.StmtParams[handle] = make(map[int]interface{})
			}
			vm.shared.StmtParams[handle][idx] = val
		}
		return value.NewNull()
	}

	vm.DefineNative("sqlite_bind_text", func(args []value.Value) value.Value {
		return bindFunc(args, args[2].String())
	})
	vm.DefineNative("sqlite_bind_float", func(args []value.Value) value.Value {
		return bindFunc(args, args[2].AsFloat)
	})
	vm.DefineNative("sqlite_bind_int", func(args []value.Value) value.Value {
		return bindFunc(args, args[2].AsInt)
	})

	vm.DefineNative("sqlite_step_exec", func(args []value.Value) value.Value {
		if len(args) < 2 {
			return value.NewNull()
		}
		stmtInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resTmplInst, ok := args[1].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resStruct := resTmplInst.Struct

		handle := int(stmtInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		stmt, ok := vm.shared.StmtHandles[handle]
		var params map[int]interface{}
		if ok {
			origParams := vm.shared.StmtParams[handle]
			params = make(map[int]interface{})
			for k, v := range origParams {
				params[k] = v
			}
		}
		vm.shared.DbLock.Unlock()

		if ok {
			// params := vm.stmtParams[handle] // Replaced by copy
			var maxIdx int
			for k := range params {
				if k > maxIdx {
					maxIdx = k
				}
			}
			argsList := make([]interface{}, maxIdx)
			for k, v := range params {
				if k > 0 && k <= maxIdx {
					argsList[k-1] = v
				}
			}
			result, err := stmt.Exec(argsList...)

			resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
			if err != nil {
				resInst.Fields["ok"] = value.NewBool(false)
				resInst.Fields["error"] = value.NewString(err.Error())
				resInst.Fields["rows_affected"] = value.NewInt(0)
				resInst.Fields["last_insert_id"] = value.NewInt(0)
			} else {
				rowsAffected, _ := result.RowsAffected()
				lastId, _ := result.LastInsertId()
				resInst.Fields["ok"] = value.NewBool(true)
				resInst.Fields["error"] = value.NewString("")
				resInst.Fields["rows_affected"] = value.NewInt(rowsAffected)
				resInst.Fields["last_insert_id"] = value.NewInt(lastId)
			}
			return value.Value{Type: value.VAL_OBJ, Obj: resInst}
		}

		resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
		resInst.Fields["ok"] = value.NewBool(false)
		resInst.Fields["error"] = value.NewString("invalid statement handle")
		resInst.Fields["rows_affected"] = value.NewInt(0)
		resInst.Fields["last_insert_id"] = value.NewInt(0)
		return value.Value{Type: value.VAL_OBJ, Obj: resInst}
	})

	vm.DefineNative("sqlite_reset", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewNull()
		}
		stmtInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		handle := int(stmtInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		defer vm.shared.DbLock.Unlock()

		if _, ok := vm.shared.StmtHandles[handle]; ok {
			vm.shared.StmtParams[handle] = make(map[int]interface{})
		}
		return value.NewNull()
	})

	vm.DefineNative("sqlite_finalize", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewNull()
		}
		stmtInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		handle := int(stmtInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		defer vm.shared.DbLock.Unlock()

		if stmt, ok := vm.shared.StmtHandles[handle]; ok {
			stmt.Close()
			delete(vm.shared.StmtHandles, handle)
			delete(vm.shared.StmtParams, handle)
		}
		return value.NewNull()
	})

	vm.DefineNative("sqlite_query", func(args []value.Value) value.Value {
		if len(args) < 4 {
			return value.NewNull()
		} // db, sql, tmplQueryResult, tmplRow

		dbInst, ok := args[0].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		sqlStr := args[1].String()

		resTmplInst, ok := args[2].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		resStruct := resTmplInst.Struct

		rowTmplInst, ok := args[3].Obj.(*value.ObjInstance)
		if !ok {
			return value.NewNull()
		}
		rowStruct := rowTmplInst.Struct

		handle := int(dbInst.Fields["handle"].AsInt)

		vm.shared.DbLock.Lock()
		db, ok := vm.shared.DbHandles[handle]
		vm.shared.DbLock.Unlock()

		if ok {
			rows, err := db.Query(sqlStr)
			if err != nil {
				// Return QueryResult with ok=false and error message
				resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
				resInst.Fields["columns"] = value.NewArray(nil)
				resInst.Fields["rows"] = value.NewArray(nil)
				resInst.Fields["row_count"] = value.NewInt(0)
				resInst.Fields["ok"] = value.NewBool(false)
				resInst.Fields["error"] = value.NewString(err.Error())
				return value.Value{Type: value.VAL_OBJ, Obj: resInst}
			}
			defer rows.Close()

			cols, _ := rows.Columns()
			colVals := make([]value.Value, len(cols))
			for i, c := range cols {
				colVals[i] = value.NewString(c)
			}

			var rowInsts []value.Value

			for rows.Next() {
				// Scan to interface{}
				dest := make([]interface{}, len(cols))
				destPtrs := make([]interface{}, len(cols))
				for i := range dest {
					destPtrs[i] = &dest[i]
				}

				rows.Scan(destPtrs...)

				rowVals := make([]value.Value, len(cols))
				for i, v := range dest {
					// Convert Go type to Noxy value
					switch tv := v.(type) {
					case nil:
						rowVals[i] = value.NewNull()
					case int64:
						rowVals[i] = value.NewInt(tv)
					case float64:
						rowVals[i] = value.NewFloat(tv)
					case string:
						rowVals[i] = value.NewString(tv)
					case []byte:
						rowVals[i] = value.NewString(string(tv))
					default:
						rowVals[i] = value.NewString(fmt.Sprintf("%v", tv))
					}
				}

				// Create Row instance
				rowInst := value.NewInstance(rowStruct).Obj.(*value.ObjInstance)
				rowInst.Fields["values"] = value.NewArray(rowVals)
				rowInsts = append(rowInsts, value.Value{Type: value.VAL_OBJ, Obj: rowInst})
			}

			// Create QueryResult instance with ok=true
			resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
			resInst.Fields["columns"] = value.NewArray(colVals)
			resInst.Fields["rows"] = value.NewArray(rowInsts)
			resInst.Fields["row_count"] = value.NewInt(int64(len(rowInsts)))
			resInst.Fields["ok"] = value.NewBool(true)
			resInst.Fields["error"] = value.NewString("")

			return value.Value{Type: value.VAL_OBJ, Obj: resInst}
		}
		// DB handle not found - return error result
		resInst := value.NewInstance(resStruct).Obj.(*value.ObjInstance)
		resInst.Fields["columns"] = value.NewArray(nil)
		resInst.Fields["rows"] = value.NewArray(nil)
		resInst.Fields["row_count"] = value.NewInt(0)
		resInst.Fields["ok"] = value.NewBool(false)
		resInst.Fields["error"] = value.NewString("invalid database handle")
		return value.Value{Type: value.VAL_OBJ, Obj: resInst}
	})

	vm.DefineNative("hex", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewNull()
		}
		if args[0].Type == value.VAL_INT {
			return value.NewString(fmt.Sprintf("0x%x", args[0].AsInt))
		}
		if args[0].Type == value.VAL_BYTES {
			return value.NewString(fmt.Sprintf("%x", args[0].Obj.(string)))
		}
		return value.NewString(args[0].String())
	})

	vm.DefineNative("hex_encode", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewString("")
		}
		arg := args[0]
		var data string
		if arg.Type == value.VAL_BYTES {
			data = arg.Obj.(string)
		} else {
			data = arg.String()
		}
		return value.NewString(hex.EncodeToString([]byte(data)))
	})

	vm.DefineNative("hex_decode", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewBytes("")
		}
		decoded, err := hex.DecodeString(args[0].String())
		if err != nil {
			return value.NewBytes("") // Or null/error? Returning empty bytes for simplicity
		}
		return value.NewBytes(string(decoded))
	})

	vm.DefineNative("base64_encode", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewString("")
		}
		arg := args[0]
		var data string
		if arg.Type == value.VAL_BYTES {
			data = arg.Obj.(string)
		} else {
			data = arg.String()
		}
		return value.NewString(base64.StdEncoding.EncodeToString([]byte(data)))
	})

	vm.DefineNative("base64_decode", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewBytes("")
		}
		decoded, err := base64.StdEncoding.DecodeString(args[0].String())
		if err != nil {
			return value.NewBytes("")
		}
		return value.NewBytes(string(decoded))
	})

	const base62Chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

	vm.DefineNative("base62_encode", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewString("")
		}
		if args[0].Type != value.VAL_INT {
			return value.NewString("")
		}
		num := args[0].AsInt
		if num == 0 {
			return value.NewString("0")
		}

		var coded []byte
		neg := false
		if num < 0 {
			neg = true
			num = -num
		}

		for num > 0 {
			rem := num % 62
			coded = append(coded, base62Chars[rem])
			num = num / 62
		}

		if neg {
			coded = append(coded, '-')
		}

		// Reverse
		for i, j := 0, len(coded)-1; i < j; i, j = i+1, j-1 {
			coded[i], coded[j] = coded[j], coded[i]
		}

		return value.NewString(string(coded))
	})

	vm.DefineNative("base62_decode", func(args []value.Value) value.Value {
		if len(args) != 1 {
			return value.NewInt(0)
		}
		str := args[0].String()
		if str == "" {
			return value.NewInt(0)
		}
		var num int64
		var neg bool
		if strings.HasPrefix(str, "-") {
			neg = true
			str = str[1:]
		}

		for _, char := range str {
			idx := strings.IndexRune(base62Chars, char)
			if idx == -1 {
				return value.NewInt(0) // Error
			}
			num = num*62 + int64(idx)
		}
		if neg {
			num = -num
		}
		return value.NewInt(num)
	})

	// Precompile regex for fmt verbs
	// Matches % [flags] [width] [.prec] verb
	// Flags: [-+ #0]
	// Width: \d+ or *
	// Prec: \. followed by \d+ or *
	// Verb: [a-zA-Z%]
	fmtVerbRe := regexp.MustCompile(`%([-+ #0]*)(?:(\d+|\*)?)(?:\.(\d+|\*))?([a-zA-Z%])`)

	vm.DefineNative("fmt", func(args []value.Value) value.Value {
		if len(args) < 1 {
			return value.NewString("")
		}
		formatStr := args[0].String()

		// Parse fmt string to handle %T specifically
		// We need to rebuild args and format string

		// Find all verbs
		matches := fmtVerbRe.FindAllStringSubmatchIndex(formatStr, -1)

		var newArgs []interface{}
		var newFormatBuilder strings.Builder

		argIdx := 0 // Index into args[1:]
		lastPos := 0

		argsData := args[1:]

		for _, match := range matches {
			// match indices: [start, end, f_start, f_end, w_start, w_end, p_start, p_end, v_start, v_end]
			start, end := match[0], match[1]
			// verb := formatStr[match[8]:match[9]]
			// We can get verb char easily
			verb := formatStr[match[8]] // byte

			// Append text before match
			newFormatBuilder.WriteString(formatStr[lastPos:start])

			// Determine if we need to consume args
			if verb == '%' {
				newFormatBuilder.WriteString("%%")
				lastPos = end
				continue
			}

			// Check if width uses arg
			// Groups are 1-indexed in concept, but indices array:
			// 0,1 whole
			// 2,3 flags (group 1)
			// 4,5 width (group 2)
			// 6,7 prec (group 3)
			// 8,9 verb (group 4)

			widthHasStar := false
			if match[4] != -1 {
				wStr := formatStr[match[4]:match[5]]
				if strings.Contains(wStr, "*") {
					widthHasStar = true
				}
			}

			precHasStar := false
			if match[6] != -1 {
				pStr := formatStr[match[6]:match[7]]
				if strings.Contains(pStr, "*") {
					precHasStar = true
				}
			}

			// Consume args for width/prec
			if widthHasStar {
				if argIdx < len(argsData) {
					newArgs = append(newArgs, argsData[argIdx].AsInt) // Assume int for width
					argIdx++
				}
			}
			if precHasStar {
				if argIdx < len(argsData) {
					newArgs = append(newArgs, argsData[argIdx].AsInt) // Assume int for prec
					argIdx++
				}
			}

			// Now handle the verb and the main arg
			if argIdx < len(argsData) {
				val := argsData[argIdx]
				argIdx++

				if verb == 'T' {
					// Replace %T with %s and supply type name string
					newFormatBuilder.WriteString("%s")

					typeName := "unknown"
					switch val.Type {
					case value.VAL_INT:
						typeName = "int"
					case value.VAL_FLOAT:
						typeName = "float"
					case value.VAL_BOOL:
						typeName = "bool"
					case value.VAL_NULL:
						typeName = "null"
					case value.VAL_BYTES:
						typeName = "bytes"
					case value.VAL_FUNCTION:
						typeName = "function"
					case value.VAL_NATIVE:
						typeName = "function"
					case value.VAL_OBJ:
						// Determine specific object type
						if _, ok := val.Obj.(*value.ObjArray); ok {
							typeName = "array"
						} else if _, ok := val.Obj.(*value.ObjMap); ok {
							typeName = "map"
						} else if inst, ok := val.Obj.(*value.ObjInstance); ok {
							typeName = inst.Struct.Name
						} else if _, ok := val.Obj.(*value.ObjStruct); ok {
							typeName = "struct" // Class definition
						} else if _, ok := val.Obj.(string); ok {
							typeName = "string"
						} else {
							typeName = fmt.Sprintf("%T", val.Obj)
						}
					}
					newArgs = append(newArgs, typeName)
				} else {
					// Keep original verb sequence (including flags/width/prec)
					newFormatBuilder.WriteString(formatStr[start:end])

					// Add argument, potentially wrapped or raw
					switch val.Type {
					case value.VAL_INT:
						newArgs = append(newArgs, val.AsInt)
					case value.VAL_FLOAT:
						newArgs = append(newArgs, val.AsFloat)
					case value.VAL_BOOL:
						newArgs = append(newArgs, val.AsBool)
					case value.VAL_NULL:
						newArgs = append(newArgs, nil)
					case value.VAL_OBJ:
						// Pass raw object
						newArgs = append(newArgs, val.Obj)
					case value.VAL_BYTES:
						newArgs = append(newArgs, value.BytesWrapper{Str: val.Obj.(string)})
					default:
						newArgs = append(newArgs, val.String())
					}
				}
			} else {
				// Not enough args? Just append remainder as literal?
				// Or Go fmt will print %!(MISSING)
				newFormatBuilder.WriteString(formatStr[start:end])
			}

			lastPos = end
		}

		// Append remaining format
		newFormatBuilder.WriteString(formatStr[lastPos:])

		return value.NewString(fmt.Sprintf(newFormatBuilder.String(), newArgs...))
	})

	return vm
}

func (vm *VM) DefineNative(name string, fn value.NativeFunc) {
	if vm.Config.SafeMode {
		if strings.HasPrefix(name, "sys_") || strings.HasPrefix(name, "sqlite_") || strings.HasPrefix(name, "io_") {
			return
		}
	}
	// Check if already defined in shared globals to avoid overwriting with thread-local closure
	if _, ok := vm.GetGlobal(name); ok {
		return
	}
	vm.SetGlobal(name, value.NewNative(name, fn))
}

func (vm *VM) SetGlobal(name string, val value.Value) {
	vm.shared.GlobalsLock.Lock()
	defer vm.shared.GlobalsLock.Unlock()
	vm.shared.Globals[name] = val
}

func (vm *VM) GetGlobal(name string) (value.Value, bool) {
	vm.shared.GlobalsLock.RLock()
	defer vm.shared.GlobalsLock.RUnlock()
	val, ok := vm.shared.Globals[name]
	return val, ok
}

func (vm *VM) SetModule(name string, val value.Value) {
	vm.shared.GlobalsLock.Lock()
	defer vm.shared.GlobalsLock.Unlock()
	vm.shared.Modules[name] = val
}

func (vm *VM) GetModule(name string) (value.Value, bool) {
	vm.shared.GlobalsLock.RLock()
	defer vm.shared.GlobalsLock.RUnlock()
	val, ok := vm.shared.Modules[name]
	return val, ok
}

func (vm *VM) Interpret(c *chunk.Chunk) error {
	// Pass nil to indicate using Shared State Globals
	return vm.InterpretWithGlobals(c, nil)
}

func (vm *VM) InterpretWithGlobals(c *chunk.Chunk, globals map[string]value.Value) error {
	scriptFn := &value.ObjFunction{
		Name:    "script",
		Arity:   0,
		Chunk:   c,
		Globals: globals,
	}

	vm.stackTop = 0
	vm.push(value.NewFunction("script", 0, 0, nil, c, globals)) // Push script function to stack slot 0

	// Call frame for script
	scriptClosure := &value.ObjClosure{Function: scriptFn, Upvalues: []*value.ObjUpvalue{}, Globals: globals}
	frame := &CallFrame{
		Closure: scriptClosure,
		IP:      0,
		Slots:   1,   // Locals start at 1
		Globals: nil, // Use nil to force fallback to Shared VM Globals (Locked)
	}

	if globals != nil && len(globals) > 0 {
		frame.Globals = globals
	} else {
		frame.Globals = nil
	}

	vm.frames[0] = frame
	vm.frameCount = 1
	vm.currentFrame = frame

	return vm.run(1)
}

func (vm *VM) run(minFrameCount int) error {
	// Cache current frame values for speed
	frame := vm.currentFrame
	c := frame.Closure.Function.Chunk.(*chunk.Chunk)
	ip := frame.IP

	for {
		if ip >= len(c.Code) {
			return nil
		}

		instruction := chunk.OpCode(c.Code[ip])
		ip++

		switch instruction {
		case chunk.OP_CONSTANT:
			// Read constant
			index := c.Code[ip]
			ip++
			constant := c.Constants[index]

			// If it's a function, bind it to current globals (Module binding)
			if constant.Type == value.VAL_FUNCTION {
				fn := constant.Obj.(*value.ObjFunction)
				// Clone to bind globals
				boundFn := &value.ObjFunction{
					Name:    fn.Name,
					Arity:   fn.Arity,
					Params:  fn.Params,
					Chunk:   fn.Chunk,
					Globals: frame.Globals,
				}
				vm.push(value.Value{Type: value.VAL_FUNCTION, Obj: boundFn})
			} else {
				vm.push(constant)
			}

		case chunk.OP_CONSTANT_LONG:
			index := int(c.Code[ip])<<8 | int(c.Code[ip+1])
			ip += 2
			constant := c.Constants[index]

			if constant.Type == value.VAL_FUNCTION {
				fn := constant.Obj.(*value.ObjFunction)
				boundFn := &value.ObjFunction{
					Name:    fn.Name,
					Arity:   fn.Arity,
					Params:  fn.Params,
					Chunk:   fn.Chunk,
					Globals: frame.Globals,
				}
				vm.push(value.Value{Type: value.VAL_FUNCTION, Obj: boundFn})
			} else {
				vm.push(constant)
			}

		case chunk.OP_NULL:
			vm.push(value.NewNull())

		case chunk.OP_JUMP:
			offset := int(c.Code[ip])<<8 | int(c.Code[ip+1])
			ip += 2
			ip += offset

		case chunk.OP_JUMP_IF_FALSE:
			offset := int(c.Code[ip])<<8 | int(c.Code[ip+1])
			ip += 2
			condition := vm.peek(0)
			if condition.Type == value.VAL_BOOL && !condition.AsBool {
				ip += offset
			}

		case chunk.OP_JUMP_IF_TRUE:
			offset := int(c.Code[ip])<<8 | int(c.Code[ip+1])
			ip += 2
			condition := vm.peek(0)
			if condition.Type == value.VAL_BOOL && condition.AsBool {
				ip += offset
			}

		case chunk.OP_LOOP:
			offset := int(c.Code[ip])<<8 | int(c.Code[ip+1])
			ip += 2
			ip -= offset

		case chunk.OP_TRUE:
			vm.push(value.NewBool(true))
		case chunk.OP_FALSE:
			vm.push(value.NewBool(false))
		case chunk.OP_POP:
			vm.LastPopped = vm.pop()

		case chunk.OP_GET_GLOBAL:
			index := c.Code[ip]
			ip++
			nameVal := c.Constants[index]
			name := nameVal.Obj.(string)

			// Try frame globals (Module scope)
			val, ok := frame.Globals[name]
			if !ok {
				// Try VM globals (Builtins / Shared)
				val, ok = vm.GetGlobal(name)
				if !ok {
					return vm.runtimeError(c, ip, "undefined global variable '%s'", name)
				}
			}
			vm.push(val)

		case chunk.OP_SET_GLOBAL:
			index := c.Code[ip]
			ip++
			nameVal := c.Constants[index]
			name := nameVal.Obj.(string)
			// Set in frame globals (Module scope)
			if frame.Globals != nil {
				frame.Globals[name] = vm.peek(0)
			} else {
				vm.SetGlobal(name, vm.peek(0))
			}

		case chunk.OP_GET_LOCAL:
			slot := c.Code[ip]
			ip++
			val := vm.stack[frame.Slots+int(slot)]
			vm.push(val)

		case chunk.OP_SET_LOCAL:
			slot := c.Code[ip]
			ip++
			vm.stack[frame.Slots+int(slot)] = vm.peek(0)

		case chunk.OP_ADD:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewInt(a.AsInt + b.AsInt))
			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_FLOAT {
				vm.push(value.NewFloat(a.AsFloat + b.AsFloat))
			} else if a.Type == value.VAL_INT && b.Type == value.VAL_FLOAT {
				vm.push(value.NewFloat(float64(a.AsInt) + b.AsFloat))

			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_INT {
				vm.push(value.NewFloat(a.AsFloat + float64(b.AsInt)))
			} else if a.Type == value.VAL_OBJ && b.Type == value.VAL_OBJ {
				// Check if both are strings
				strA, okA := a.Obj.(string)
				strB, okB := b.Obj.(string)
				if okA && okB {
					vm.push(value.NewString(strA + strB))
					continue // Added continue for cleaner flow
				}
				// Check if both are BYTES?
				// VAL_BYTES has Obj as string currently.
				// But Type is VAL_BYTES.
				// Wait, if Type is VAL_BYTES, Obj is string.
				// Logic:
				if a.Type == value.VAL_BYTES && b.Type == value.VAL_BYTES {
					vm.push(value.NewBytes(a.Obj.(string) + b.Obj.(string)))
					continue
				}

				return vm.runtimeError(c, ip, "operands must be numbers, strings or bytes")
			} else if a.Type == value.VAL_BYTES && b.Type == value.VAL_BYTES {
				// Case where types are explicit VAL_BYTES (not VAL_OBJ)
				vm.push(value.NewBytes(a.Obj.(string) + b.Obj.(string)))
			} else {
				return vm.runtimeError(c, ip, "operands must be numbers or strings or bytes")
			}

		case chunk.OP_ADD_INT:
			// Inline pop/pop/push for optimization
			// b is at stackTop-1, a is at stackTop-2
			// result replaces a (at stackTop-2)
			// b (at stackTop-1) is cleared
			// stackTop decrements by 1
			vm.stack[vm.stackTop-2] = value.NewInt(vm.stack[vm.stackTop-2].AsInt + vm.stack[vm.stackTop-1].AsInt)
			vm.stack[vm.stackTop-1] = value.Value{}
			vm.stackTop--

		case chunk.OP_SUBTRACT:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewInt(a.AsInt - b.AsInt))
			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_FLOAT {
				vm.push(value.NewFloat(a.AsFloat - b.AsFloat))
			} else if a.Type == value.VAL_INT && b.Type == value.VAL_FLOAT {
				vm.push(value.NewFloat(float64(a.AsInt) - b.AsFloat))
			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_INT {
				vm.push(value.NewFloat(a.AsFloat - float64(b.AsInt)))
			} else {
				return vm.runtimeError(c, ip, "operands must be numbers")
			}
		case chunk.OP_SUB_INT:
			b := vm.pop()
			a := vm.pop()
			vm.push(value.NewInt(a.AsInt - b.AsInt))
		case chunk.OP_MULTIPLY:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewInt(a.AsInt * b.AsInt))
			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_FLOAT {
				vm.push(value.NewFloat(a.AsFloat * b.AsFloat))
			} else if a.Type == value.VAL_INT && b.Type == value.VAL_FLOAT {
				vm.push(value.NewFloat(float64(a.AsInt) * b.AsFloat))
			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_INT {
				vm.push(value.NewFloat(a.AsFloat * float64(b.AsInt)))
			} else {
				return vm.runtimeError(c, ip, "operands must be numbers")
			}
		case chunk.OP_MUL_INT:
			b := vm.pop()
			a := vm.pop()
			vm.push(value.NewInt(a.AsInt * b.AsInt))
		case chunk.OP_DIVIDE:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				if b.AsInt == 0 {
					return vm.runtimeError(c, ip, "division by zero")
				}
				vm.push(value.NewInt(a.AsInt / b.AsInt))
			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_FLOAT {
				if b.AsFloat == 0 {
					return vm.runtimeError(c, ip, "division by zero")
				}
				vm.push(value.NewFloat(a.AsFloat / b.AsFloat))
			} else if a.Type == value.VAL_INT && b.Type == value.VAL_FLOAT {
				if b.AsFloat == 0 {
					return vm.runtimeError(c, ip, "division by zero")
				}
				vm.push(value.NewFloat(float64(a.AsInt) / b.AsFloat))
			} else if a.Type == value.VAL_FLOAT && b.Type == value.VAL_INT {
				if b.AsInt == 0 {
					return vm.runtimeError(c, ip, "division by zero")
				}
				vm.push(value.NewFloat(a.AsFloat / float64(b.AsInt)))
			} else {
				return vm.runtimeError(c, ip, "operands must be numbers")
			}
		case chunk.OP_DIV_INT:
			b := vm.pop()
			a := vm.pop()
			if b.AsInt == 0 {
				return vm.runtimeError(c, ip, "division by zero")
			}
			vm.push(value.NewInt(a.AsInt / b.AsInt))
		case chunk.OP_LEN:
			val := vm.pop()
			if val.Type == value.VAL_OBJ {
				if arr, ok := val.Obj.(*value.ObjArray); ok {
					vm.push(value.NewInt(int64(len(arr.Elements))))
				} else if m, ok := val.Obj.(*value.ObjMap); ok {
					vm.push(value.NewInt(int64(len(m.Data))))
				} else if s, ok := val.Obj.(string); ok {
					vm.push(value.NewInt(int64(len(s))))
				} else {
					vm.push(value.NewInt(0)) // Or error?
				}
			} else if val.Type == value.VAL_BYTES {
				// Bytes stored as string in Obj
				s := val.Obj.(string)
				vm.push(value.NewInt(int64(len(s))))
			} else {
				vm.push(value.NewInt(0))
			}

		case chunk.OP_SELECT:
			count := int(c.Code[ip])
			ip++
			cases := make([]reflect.SelectCase, count)
			// Stack layout: [... Case0_Chan, Case0_Val, Case0_Mode ... CaseN_Chan, CaseN_Val, CaseN_Mode]
			// Top is CaseN_Mode.
			// Iterating i from count-1 down to 0:
			for i := count - 1; i >= 0; i-- {
				mode := vm.pop().AsInt
				val := vm.pop()
				chVal := vm.pop()

				if mode == 2 { // Default
					cases[i] = reflect.SelectCase{Dir: reflect.SelectDefault}
				} else if mode == 1 { // Send
					if chVal.Type != value.VAL_CHANNEL {
						return vm.runtimeError(c, ip, "select case expects channel")
					}
					ch := chVal.Obj.(*value.ObjChannel).Chan
					cases[i] = reflect.SelectCase{Dir: reflect.SelectSend, Chan: reflect.ValueOf(ch), Send: reflect.ValueOf(val)}
				} else { // Recv
					if chVal.Type != value.VAL_CHANNEL {
						return vm.runtimeError(c, ip, "select case expects channel")
					}
					ch := chVal.Obj.(*value.ObjChannel).Chan
					cases[i] = reflect.SelectCase{Dir: reflect.SelectRecv, Chan: reflect.ValueOf(ch)}
				}
			}

			chosenIndex, recvVal, recvOK := reflect.Select(cases)

			vm.push(value.NewInt(int64(chosenIndex)))

			var valToPush value.Value
			if recvOK {
				if v, ok := recvVal.Interface().(value.Value); ok {
					valToPush = v
				} else {
					valToPush = value.NewNull()
				}
			} else {
				valToPush = value.NewNull()
			}
			vm.push(valToPush)
			vm.push(value.NewBool(recvOK))

		case chunk.OP_MODULO:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				if b.AsInt == 0 {
					return vm.runtimeError(c, ip, "modulo by zero")
				}
				vm.push(value.NewInt(a.AsInt % b.AsInt))
			} else {
				return vm.runtimeError(c, ip, "operands for %% must be integers")
			}
		case chunk.OP_MOD_INT:
			// Inline pop/pop/push
			b := vm.stack[vm.stackTop-1].AsInt
			a := vm.stack[vm.stackTop-2].AsInt
			if b == 0 {
				return vm.runtimeError(c, ip, "modulo by zero")
			}
			vm.stack[vm.stackTop-2] = value.NewInt(a % b)
			vm.stack[vm.stackTop-1] = value.Value{}
			vm.stackTop--

		case chunk.OP_BIT_AND:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewInt(a.AsInt & b.AsInt))
			} else if a.Type == value.VAL_BYTES && b.Type == value.VAL_BYTES {
				sA := a.Obj.(string)
				sB := b.Obj.(string)
				if len(sA) != len(sB) {
					return vm.runtimeError(c, ip, "operands for & must have same length")
				}
				res := make([]byte, len(sA))
				for i := 0; i < len(sA); i++ {
					res[i] = sA[i] & sB[i]
				}
				vm.push(value.NewBytes(string(res)))
			} else {
				return vm.runtimeError(c, ip, "operands for & must be integers or bytes")
			}

		case chunk.OP_BIT_OR:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewInt(a.AsInt | b.AsInt))
			} else if a.Type == value.VAL_BYTES && b.Type == value.VAL_BYTES {
				sA := a.Obj.(string)
				sB := b.Obj.(string)
				if len(sA) != len(sB) {
					return vm.runtimeError(c, ip, "operands for | must have same length")
				}
				res := make([]byte, len(sA))
				for i := 0; i < len(sA); i++ {
					res[i] = sA[i] | sB[i]
				}
				vm.push(value.NewBytes(string(res)))
			} else {
				return vm.runtimeError(c, ip, "operands for | must be integers or bytes")
			}

		case chunk.OP_BIT_XOR:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewInt(a.AsInt ^ b.AsInt))
			} else if a.Type == value.VAL_BYTES && b.Type == value.VAL_BYTES {
				sA := a.Obj.(string)
				sB := b.Obj.(string)
				if len(sA) != len(sB) {
					return vm.runtimeError(c, ip, "operands for ^ must have same length")
				}
				res := make([]byte, len(sA))
				for i := 0; i < len(sA); i++ {
					res[i] = sA[i] ^ sB[i]
				}
				vm.push(value.NewBytes(string(res)))
			} else {
				return vm.runtimeError(c, ip, "operands for ^ must be integers or bytes")
			}

		case chunk.OP_BIT_NOT:
			a := vm.pop()
			if a.Type == value.VAL_INT {
				vm.push(value.NewInt(^a.AsInt))
			} else if a.Type == value.VAL_BYTES {
				sA := a.Obj.(string)
				res := make([]byte, len(sA))
				for i := 0; i < len(sA); i++ {
					res[i] = ^sA[i]
				}
				vm.push(value.NewBytes(string(res)))
			} else {
				return vm.runtimeError(c, ip, "operand for ~ must be integer or bytes")
			}

		case chunk.OP_SHIFT_LEFT:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				if b.AsInt < 0 {
					return vm.runtimeError(c, ip, "negative shift count")
				}
				vm.push(value.NewInt(a.AsInt << uint64(b.AsInt)))
			} else {
				return vm.runtimeError(c, ip, "operands for << must be integers")
			}

		case chunk.OP_SHIFT_RIGHT:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				if b.AsInt < 0 {
					return vm.runtimeError(c, ip, "negative shift count")
				}
				vm.push(value.NewInt(a.AsInt >> uint64(b.AsInt)))
			} else {
				return vm.runtimeError(c, ip, "operands for >> must be integers")
			}
		case chunk.OP_NEGATE:
			v := vm.pop()
			if v.Type == value.VAL_INT {
				vm.push(value.NewInt(-v.AsInt))
			} else if v.Type == value.VAL_FLOAT {
				vm.push(value.NewFloat(-v.AsFloat))
			} else {
				return vm.runtimeError(c, ip, "operand must be number")
			}
		case chunk.OP_NOT:
			v := vm.pop()
			if v.Type == value.VAL_BOOL {
				vm.push(value.NewBool(!v.AsBool))
			} else {
				return vm.runtimeError(c, ip, "operand must be boolean")
			}
		case chunk.OP_AND:
			b := vm.pop()
			a := vm.pop()
			// Assuming strict boolean for & operator as per usage in 'if'
			// Or should we support truthiness?
			// binary_tree.nx usage: if condition | condition. Conditions are bool.
			// Let's coerce to bool if needed or error. Safe to error for now.
			if a.Type == value.VAL_BOOL && b.Type == value.VAL_BOOL {
				vm.push(value.NewBool(a.AsBool && b.AsBool))
			} else {
				return vm.runtimeError(c, ip, "operands for & must be boolean")
			}
		case chunk.OP_OR:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_BOOL && b.Type == value.VAL_BOOL {
				vm.push(value.NewBool(a.AsBool || b.AsBool))
			} else {
				return vm.runtimeError(c, ip, "operands for | must be boolean")
			}
		case chunk.OP_ZEROS:
			countVal := vm.pop()
			if countVal.Type != value.VAL_INT {
				return vm.runtimeError(c, ip, "zeros size must be integer")
			}
			count := int(countVal.AsInt)
			elements := make([]value.Value, count)
			for i := 0; i < count; i++ {
				elements[i] = value.NewInt(0)
			}
			vm.push(value.NewArray(elements))
		case chunk.OP_GREATER:
			b := vm.pop()
			a := vm.pop()
			// Only supporting int/float comparison for now
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewBool(a.AsInt > b.AsInt))
			} else {
				// TODO: floats
				vm.push(value.NewBool(false))
			}
		case chunk.OP_GREATER_INT:
			b := vm.pop()
			a := vm.pop()
			vm.push(value.NewBool(a.AsInt > b.AsInt))
		case chunk.OP_LESS:
			b := vm.pop()
			a := vm.pop()
			if a.Type == value.VAL_INT && b.Type == value.VAL_INT {
				vm.push(value.NewBool(a.AsInt < b.AsInt))
			} else {
				vm.push(value.NewBool(false))
			}
		case chunk.OP_LESS_INT:
			// Inline pop/pop/push
			vm.stack[vm.stackTop-2] = value.NewBool(vm.stack[vm.stackTop-2].AsInt < vm.stack[vm.stackTop-1].AsInt)
			vm.stack[vm.stackTop-1] = value.Value{}
			vm.stackTop--
		case chunk.OP_EQUAL:
			b := vm.pop()
			a := vm.pop()
			vm.push(value.NewBool(valuesEqual(a, b)))
		case chunk.OP_EQUAL_INT:
			b := vm.pop()
			a := vm.pop()
			vm.push(value.NewBool(a.AsInt == b.AsInt))
		case chunk.OP_PRINT:
			// v := vm.pop()
			// fmt.Println(v)
			// Replaced by native function 'print' call usually, but for now we keep OP_PRINT for debug?
			// But user wants `print()`. OP_PRINT in Noxy was statement `print x`.
			// If we support `print(x)`, it is a function call.
			// Let's keep OP_PRINT logic for now if compiler emits it for statement `print`.
			// But wait, Noxy doesn't have `print` keyword statement. It's a builtin function.
			// So OP_PRINT opcode might be deprecated or used for `print` keyword if we added one.
			// Reverting to popping and printing for debug.
			v := vm.pop()
			fmt.Println(v)

		case chunk.OP_CALL:
			argCount := int(c.Code[ip])
			ip++

			frame.IP = ip // Save current instruction pointer to the frame before call

			if ok, err := vm.callValue(vm.peek(argCount), argCount, c, ip); !ok {
				return err
			}
			// Update cached frame
			frame = vm.currentFrame // Switch to new frame
			c = frame.Closure.Function.Chunk.(*chunk.Chunk)
			ip = frame.IP

		case chunk.OP_CLOSURE:
			idx := c.Code[ip]
			ip++
			fnVal := c.Constants[idx]
			fn := fnVal.Obj.(*value.ObjFunction)

			closure := &value.ObjClosure{
				Function: fn,
				Upvalues: make([]*value.ObjUpvalue, fn.UpvalueCount),
				Globals:  frame.Globals,
			}

			for i := 0; i < fn.UpvalueCount; i++ {
				isLocal := c.Code[ip]
				ip++
				index := c.Code[ip]
				ip++

				if isLocal == 1 {
					closure.Upvalues[i] = vm.captureUpvalue(&vm.stack[frame.Slots+int(index)])
				} else {
					closure.Upvalues[i] = frame.Closure.Upvalues[index]
				}
			}
			vm.push(value.Value{Type: value.VAL_FUNCTION, Obj: closure})

		case chunk.OP_GET_UPVALUE:
			slot := c.Code[ip]
			ip++
			val := *frame.Closure.Upvalues[slot].Location
			vm.push(val)

		case chunk.OP_SET_UPVALUE:
			slot := c.Code[ip]
			ip++
			*frame.Closure.Upvalues[slot].Location = vm.peek(0)

		case chunk.OP_CLOSE_UPVALUE:
			vm.closeUpvalue(&vm.stack[vm.stackTop-1])
			vm.pop()

		case chunk.OP_RETURN:
			// Return from function

			// 1. Pop result
			result := vm.pop()
			calleeFrame := vm.currentFrame

			// 2. Clear the stack range used by the function (args + locals)
			// This is CRITICAL for GC. We must nullify the references.
			// calleeFrame.Slots points to the function object itself.
			// We iterate up to stackTop (which is where result WAS before pop).
			for i := calleeFrame.Slots; i < vm.stackTop; i++ {
				vm.closeUpvalue(&vm.stack[i]) // Close any upvalues pointing to this slot
				vm.stack[i] = value.Value{}
			}

			// 3. Decrement frame count
			vm.frameCount--

			// 4. Update current frame pointer
			if vm.frameCount > 0 {
				vm.currentFrame = vm.frames[vm.frameCount-1]
			} else {
				vm.currentFrame = nil
			}

			// 5. Return from run() if we drop below call depth
			if vm.frameCount < minFrameCount {
				// We are exiting the run loop.
				// We need to place result at the location expected by the caller.
				// The caller expects the function and args to be consumed, and result pushed.
				// calleeFrame.Slots is the start of the window (Function object).
				vm.stackTop = calleeFrame.Slots
				vm.push(result)
				return nil
			}

			// 6. Restore execution context
			frame = vm.currentFrame
			vm.stackTop = calleeFrame.Slots // Drop args/locals/function from stackTop
			vm.push(result)                 // Push result replacing the function

			c = frame.Closure.Function.Chunk.(*chunk.Chunk)
			ip = frame.IP

		case chunk.OP_ARRAY:
			count := int(c.Code[ip])<<8 | int(c.Code[ip+1])
			ip += 2

			elements := make([]value.Value, count)
			for i := count - 1; i >= 0; i-- {
				elements[i] = vm.pop()
			}
			vm.push(value.NewArray(elements))

		case chunk.OP_MAP:
			count := int(c.Code[ip])<<8 | int(c.Code[ip+1])
			ip += 2

			// Map expects keys and values on stack: K1, V1, K2, V2...
			mapObj := value.NewMap()
			mapData := mapObj.Obj.(*value.ObjMap).Data

			for i := 0; i < count; i++ {
				val := vm.pop()
				keyVal := vm.pop()

				var key interface{}
				if keyVal.Type == value.VAL_INT {
					key = keyVal.AsInt
				} else if keyVal.Type == value.VAL_OBJ {
					if str, ok := keyVal.Obj.(string); ok {
						key = str
					} else {
						return vm.runtimeError(c, ip, "map key must be int or string")
					}
				} else {
					return vm.runtimeError(c, ip, "map key must be int or string")
				}
				mapData[key] = val
			}
			vm.push(mapObj)

		case chunk.OP_DUP:
			vm.push(vm.peek(0))

		case chunk.OP_IMPORT:
			index := c.Code[ip]
			ip++
			nameConstant := c.Constants[index]
			moduleName := nameConstant.Obj.(string)

			// Check cache
			if mod, ok := vm.GetModule(moduleName); ok {
				vm.push(mod)
			} else {
				mod, err := vm.loadModule(moduleName)
				if err != nil {
					return vm.runtimeError(c, ip, "failed to import module '%s': %v", moduleName, err)
				}
				vm.SetModule(moduleName, mod)
				vm.push(mod)
			}

			// Refresh frame if import caused GC or stack moves (unlikely but safe)
			// And if recursive run changed things?
			frame = vm.currentFrame
			// c/ip are from frame. c/ip in local vars are stale?
			// frame IS vm.currentFrame.
			// After loadModule, frame is valid (frames[0]).
			// c/ip valid.
			// But to be safe:
			// frame = vm.currentFrame -- Done.

		case chunk.OP_IMPORT_FROM_ALL:
			modVal := vm.pop()
			if modVal.Type == value.VAL_OBJ {
				if modMap, ok := modVal.Obj.(*value.ObjMap); ok {
					for k, v := range modMap.Data {
						if keyStr, ok := k.(string); ok {
							vm.SetGlobal(keyStr, v)
						}
					}
				} else {
					return vm.runtimeError(c, ip, "import * expected a module (map)")
				}
			} else {
				return vm.runtimeError(c, ip, "import * expected a module object")
			}

		case chunk.OP_GET_INDEX:
			indexVal := vm.pop()
			collectionVal := vm.pop()

			if collectionVal.Type == value.VAL_OBJ {
				if arr, ok := collectionVal.Obj.(*value.ObjArray); ok {
					if indexVal.Type != value.VAL_INT {
						return vm.runtimeError(c, ip, "array index must be integer")
					}
					idx := int(indexVal.AsInt)
					if idx < 0 || idx >= len(arr.Elements) {
						return vm.runtimeError(c, ip, "array index out of bounds")
					}
					vm.push(arr.Elements[idx])
					continue
				} else if mapObj, ok := collectionVal.Obj.(*value.ObjMap); ok {
					var key interface{}
					if indexVal.Type == value.VAL_INT {
						key = indexVal.AsInt
					} else if indexVal.Type == value.VAL_OBJ {
						if str, ok := indexVal.Obj.(string); ok {
							key = str
						} else {
							return vm.runtimeError(c, ip, "map key must be int or string")
						}
					} else {
						return vm.runtimeError(c, ip, "map key must be int or string")
					}

					val, ok := mapObj.Data[key]
					if !ok {
						// Return null or error? Spec says null for missing key? Or error?
						// "has_key" exists. Missing key usually runtime error or null.
						// Let's return Null for now, similar to dynamic languages.
						vm.push(value.NewNull())
					} else {
						vm.push(val)
					}
					continue
				} else if str, ok := collectionVal.Obj.(string); ok {
					// String indexing
					if indexVal.Type != value.VAL_INT {
						return vm.runtimeError(c, ip, "string index must be integer")
					}
					idx := int(indexVal.AsInt)
					if idx < 0 || idx >= len(str) {
						return vm.runtimeError(c, ip, "string index out of bounds")
					}
					vm.push(value.NewString(string(str[idx])))
					continue
				}
			}
			// Check if it's a bytes value
			if collectionVal.Type == value.VAL_BYTES {
				str := collectionVal.Obj.(string)
				if indexVal.Type != value.VAL_INT {
					return vm.runtimeError(c, ip, "bytes index must be integer")
				}
				idx := int(indexVal.AsInt)
				if idx < 0 || idx >= len(str) {
					return vm.runtimeError(c, ip, "bytes index out of bounds")
				}
				vm.push(value.NewInt(int64(str[idx])))
				continue
			}
			return vm.runtimeError(c, ip, "cannot index non-array/map/bytes")

		case chunk.OP_SET_INDEX:
			val := vm.pop()
			indexVal := vm.pop()
			collectionVal := vm.pop() // The array/map itself is on stack (pointer)

			if collectionVal.Type == value.VAL_OBJ {
				if arr, ok := collectionVal.Obj.(*value.ObjArray); ok {
					if indexVal.Type != value.VAL_INT {
						return vm.runtimeError(c, ip, "array index must be integer")
					}
					idx := int(indexVal.AsInt)
					if idx < 0 || idx >= len(arr.Elements) {
						return vm.runtimeError(c, ip, "array index out of bounds")
					}
					arr.Elements[idx] = val
					vm.push(val) // Assignment expression result
					continue
				} else if mapObj, ok := collectionVal.Obj.(*value.ObjMap); ok {
					var key interface{}
					if indexVal.Type == value.VAL_INT {
						key = indexVal.AsInt
					} else if indexVal.Type == value.VAL_OBJ {
						if str, ok := indexVal.Obj.(string); ok {
							key = str
						} else {
							return vm.runtimeError(c, ip, "map key must be int or string")
						}
					} else {
						return vm.runtimeError(c, ip, "map key must be int or string")
					}
					mapObj.Data[key] = val
					vm.push(val)
					continue
				}
			}
			return vm.runtimeError(c, ip, "cannot set index on non-array/map")

		case chunk.OP_GET_PROPERTY:
			index := c.Code[ip]
			ip++
			nameVal := c.Constants[index]
			name := nameVal.Obj.(string)

			instanceVal := vm.pop()
			if instanceVal.Type != value.VAL_OBJ {
				return vm.runtimeError(c, ip, "only instances/maps have properties")
			}

			if instance, ok := instanceVal.Obj.(*value.ObjInstance); ok {
				val, ok := instance.Fields[name]
				if !ok {
					return vm.runtimeError(c, ip, "undefined property '%s'", name)
				}
				vm.push(val)
			} else if mapObj, ok := instanceVal.Obj.(*value.ObjMap); ok {
				// Allow accessing map keys as properties (for modules)
				val, ok := mapObj.Data[name]
				if !ok {
					return vm.runtimeError(c, ip, "undefined property '%s' in module/map", name)
				}
				vm.push(val)
			} else {
				return vm.runtimeError(c, ip, "only instances and maps have properties")
			}

		case chunk.OP_SET_PROPERTY:
			index := c.Code[ip]
			ip++
			nameVal := c.Constants[index]
			name := nameVal.Obj.(string)

			val := vm.pop()
			instanceVal := vm.pop()

			if instanceVal.Type != value.VAL_OBJ {
				return vm.runtimeError(c, ip, "only instances have properties")
			}
			instance, ok := instanceVal.Obj.(*value.ObjInstance)
			if !ok {
				return vm.runtimeError(c, ip, "only instances have properties")
			}

			instance.Fields[name] = val
			vm.push(val)
		}
	}
}

func (vm *VM) callValue(callee value.Value, argCount int, c *chunk.Chunk, ip int) (bool, error) {
	if callee.Type == value.VAL_OBJ {
		if structDef, ok := callee.Obj.(*value.ObjStruct); ok {
			// Instantiate
			if argCount != len(structDef.Fields) {
				return false, vm.runtimeError(c, ip, "expected %d arguments for struct %s but got %d", len(structDef.Fields), structDef.Name, argCount)
			}

			instance := value.NewInstance(structDef)
			instObj := instance.Obj.(*value.ObjInstance)

			// Args are on stack.
			for i := 0; i < argCount; i++ {
				arg := vm.peek(argCount - 1 - i)
				fieldName := structDef.Fields[i]
				instObj.Fields[fieldName] = arg
			}

			// Pop args AND callee (struct def)
			vm.stackTop -= argCount + 1
			// Push instance
			vm.push(instance)
			return true, nil
		}
	}
	if callee.Type == value.VAL_FUNCTION {
		return vm.call(callee.Obj.(*value.ObjClosure), argCount, c, ip)
	}
	if callee.Type == value.VAL_NATIVE {
		native := callee.Obj.(*value.ObjNative)
		args := vm.stack[vm.stackTop-argCount : vm.stackTop]
		// fmt.Printf("Calling native %s with args: %v\n", native.Name, args)
		result := native.Fn(args)
		vm.stackTop -= argCount + 1 // args + function
		vm.push(result)
		return true, nil
	}
	return false, vm.runtimeError(c, ip, "can only call functions and classes")
}

func (vm *VM) call(closure *value.ObjClosure, argCount int, c *chunk.Chunk, ip int) (bool, error) {
	// fmt.Printf("Calling function %s, code len: %d\n", fn.Name, len(chunk.Code))

	fn := closure.Function

	if argCount != fn.Arity {
		return false, vm.runtimeError(c, ip, "expected %d arguments but got %d", fn.Arity, argCount)
	}

	if vm.frameCount == FramesMax {
		return false, vm.runtimeError(c, ip, "stack overflow")
	}

	// Handle Pass-by-Value (Copy) for non-ref parameters
	// Args are at vm.stackTop - argCount
	baseArgs := vm.stackTop - argCount
	for i := 0; i < argCount; i++ {
		if i < len(fn.Params) {
			param := fn.Params[i]
			if !param.IsRef {
				// Pass by Value: Copy if mutable object
				val := vm.stack[baseArgs+i]
				vm.stack[baseArgs+i] = vm.copyValue(val)
			}
		}
	}

	frame := &CallFrame{
		Closure: closure,
		IP:      0,
		Slots:   vm.stackTop - argCount - 1, // Start of locals window (fn + args)
		Globals: closure.Globals,
	}
	// Push new frame
	vm.frames[vm.frameCount] = frame
	vm.frameCount++
	vm.currentFrame = frame
	return true, nil
}

func (vm *VM) copyValue(v value.Value) value.Value {
	if v.Type != value.VAL_OBJ {
		return v
	}
	switch obj := v.Obj.(type) {
	case *value.ObjArray:
		newElems := make([]value.Value, len(obj.Elements))
		copy(newElems, obj.Elements)
		return value.Value{Type: value.VAL_OBJ, Obj: &value.ObjArray{Elements: newElems}}
	case *value.ObjMap:
		newData := make(map[interface{}]value.Value)
		for k, val := range obj.Data {
			newData[k] = val
		}
		return value.Value{Type: value.VAL_OBJ, Obj: &value.ObjMap{Data: newData}}
	case *value.ObjInstance:
		newFields := make(map[string]value.Value)
		for k, val := range obj.Fields {
			newFields[k] = val
		}
		return value.Value{Type: value.VAL_OBJ, Obj: &value.ObjInstance{Struct: obj.Struct, Fields: newFields}}
	default:
		return v
	}
}

func (vm *VM) readShort() uint16 {
	vm.ip += 2
	return uint16(vm.chunk.Code[vm.ip-2])<<8 | uint16(vm.chunk.Code[vm.ip-1])
}

// isFalsey returns true if the value is false or null
func isFalsey(v value.Value) bool {
	return v.Type == value.VAL_NULL || (v.Type == value.VAL_BOOL && !v.AsBool)
}

func valuesEqual(a, b value.Value) bool {
	if a.Type != b.Type {
		return false
	}
	switch a.Type {
	case value.VAL_BOOL:
		return a.AsBool == b.AsBool
	case value.VAL_NULL:
		return true
	case value.VAL_INT:
		return a.AsInt == b.AsInt
	case value.VAL_FLOAT:
		return a.AsFloat == b.AsFloat
	case value.VAL_OBJ:
		return a.Obj == b.Obj // Simple pointer/string comparison
	case value.VAL_BYTES:
		return a.Obj.(string) == b.Obj.(string)
	default:
		return false
	}
}

func (vm *VM) readConstant() value.Value {
	// Assumes 1 byte operand for constant index
	index := vm.chunk.Code[vm.ip]
	vm.ip++
	return vm.chunk.Constants[index]
}

func (vm *VM) push(v value.Value) {
	if vm.stackTop >= StackMax {
		panic("Stack overflow")
	}
	vm.stack[vm.stackTop] = v
	vm.stackTop++
}

func (vm *VM) pop() value.Value {
	vm.stackTop--
	val := vm.stack[vm.stackTop]
	vm.stack[vm.stackTop] = value.Value{} // Clear reference to help GC
	return val
}

func (vm *VM) loadModule(name string) (value.Value, error) {
	// Convert dot notation to path path separator
	pathName := strings.ReplaceAll(name, ".", string(filepath.Separator))

	// Search paths candidates (File .nx OR Directory)
	// We prefer file over directory if both exist? usually explicit file wins.
	// But let's check both possibilities.

	var path string
	var isDir bool
	// found := false // Unused

	// Helper to check 4 locations
	checkLocations := func(suffix string) bool {
		candidates := []string{
			filepath.Join(vm.Config.RootPath, "stdlib", suffix),
			filepath.Join(vm.Config.RootPath, suffix),
			filepath.Join("stdlib", suffix),
			suffix,
		}
		for _, p := range candidates {
			info, err := os.Stat(p)
			if err == nil {
				path = p
				isDir = info.IsDir()
				// found = true
				return true
			}
		}
		return false
	}

	// 1. Check for .nx file
	if checkLocations(pathName+".nx") && !isDir {
		// Found file
	} else if checkLocations(pathName) && isDir {
		// Found directory (on disk)
	} else {
		// Not found on disk, check embedded stdlib
		// Stdlib is flat in embed.go usually? Or structure preserved?
		// We moved stdlib/* to internal/stdlib.
		// So internal/stdlib has *.nx files directly.
		// Name would be "time" "io" etc.
		// pathName for "time" is "time".
		// embedded file is "time.nx".

		// Check if it exists in embedded FS
		embedPath := pathName + ".nx"
		content, err := stdlib.FS.ReadFile(embedPath)
		if err == nil {
			// Found in embedded stdlib!
			l := lexer.New(string(content))
			p := parser.New(l)
			prog := p.ParseProgram()
			if len(p.Errors()) > 0 {
				return value.NewNull(), fmt.Errorf("parse error in embedded module %s: %v", name, p.Errors())
			}
			c := compiler.NewWithState(make(map[string]ast.NoxyType), embedPath)
			chunk, _, err := c.Compile(prog)
			if err != nil {
				return value.NewNull(), err
			}
			moduleGlobals := make(map[string]value.Value)
			modFn := &value.ObjFunction{
				Name:    name,
				Arity:   0,
				Chunk:   chunk,
				Globals: moduleGlobals,
			}
			modClosure := &value.ObjClosure{Function: modFn, Upvalues: []*value.ObjUpvalue{}, Globals: moduleGlobals}
			modVal := value.Value{Type: value.VAL_FUNCTION, Obj: modClosure}
			vm.push(modVal)
			if ok, err := vm.callValue(modVal, 0, nil, 0); !ok {
				return value.NewNull(), err
			}
			err = vm.run(vm.frameCount) // Run until return
			if err != nil {
				return value.NewNull(), err
			}
			vm.pop() // Pop result
			return value.NewMapWithData(moduleGlobals), nil
		}

		return value.NewNull(), fmt.Errorf("module not found: %s", name)
	}

	// Case 1: Directory Import (Implicit Module)
	if isDir {
		files, err := os.ReadDir(path)
		if err != nil {
			return value.NewNull(), err
		}

		moduleGlobals := make(map[string]value.Value)

		for _, f := range files {
			if f.IsDir() {
				// Recursively load subdirectory as a nested module
				subDirName := name + "." + f.Name()
				subMod, err := vm.loadModule(subDirName)
				if err != nil {
					// Ignore subdirectories that fail to load (e.g., empty or invalid)
					continue
				}
				moduleGlobals[f.Name()] = subMod
			} else if strings.HasSuffix(f.Name(), ".nx") {
				baseName := strings.TrimSuffix(f.Name(), ".nx")
				subModuleName := name + "." + baseName

				// Recursive load
				subMod, err := vm.loadModule(subModuleName)
				if err != nil {
					return value.NewNull(), fmt.Errorf("failed to load submodule %s: %v", subModuleName, err)
				}
				moduleGlobals[baseName] = subMod
			}
		}
		return value.NewMapWithData(moduleGlobals), nil
	}

	// Case 2: File Import
	content, err := os.ReadFile(path)
	if err != nil {
		return value.NewNull(), err
	}

	l := lexer.New(string(content))
	p := parser.New(l)
	prog := p.ParseProgram()
	if len(p.Errors()) > 0 {
		return value.NewNull(), fmt.Errorf("parse error in module %s: %v", name, p.Errors())
	}

	c := compiler.NewWithState(make(map[string]ast.NoxyType), path)
	chunk, _, err := c.Compile(prog)
	if err != nil {
		return value.NewNull(), err
	}

	// Create isolated Module Globals
	moduleGlobals := make(map[string]value.Value)

	// Prepare Module Function
	modFn := &value.ObjFunction{
		Name:    name,
		Arity:   0,
		Chunk:   chunk,
		Globals: moduleGlobals,
	}
	modClosure := &value.ObjClosure{Function: modFn, Upvalues: []*value.ObjUpvalue{}, Globals: moduleGlobals}
	modVal := value.Value{Type: value.VAL_FUNCTION, Obj: modClosure}

	// Execute Module Synchronously
	vm.push(modVal)
	if ok, err := vm.callValue(modVal, 0, nil, 0); !ok {
		return value.NewNull(), err
	}

	// Run until this frame returns
	startFrameCount := vm.frameCount
	err = vm.run(startFrameCount)
	if err != nil {
		return value.NewNull(), err
	}

	// Module execution finished.
	// The result of module (usually null) is on stack. Pop it.
	vm.pop()

	// Return the Module Map
	return value.NewMapWithData(moduleGlobals), nil
}

func (vm *VM) peek(distance int) value.Value {
	return vm.stack[vm.stackTop-1-distance]
}

// captureUpvalue finds or creates an open upvalue for the given stack slot.
func (vm *VM) captureUpvalue(local *value.Value) *value.ObjUpvalue {
	// var prevUpvalue *value.ObjUpvalue // Unused for now
	upvalue := vm.openUpvalues

	// Walk list
	for upvalue != nil && upvalue.Location != local {
		// prevUpvalue = upvalue
		upvalue = upvalue.Next
	}

	if upvalue != nil && upvalue.Location == local {
		return upvalue
	}

	createdUpvalue := &value.ObjUpvalue{
		Location: local,
		Next:     vm.openUpvalues,
	}
	vm.openUpvalues = createdUpvalue

	return createdUpvalue
}

func (vm *VM) closeUpvalue(slot *value.Value) {
	var prev *value.ObjUpvalue
	curr := vm.openUpvalues

	for curr != nil {
		if curr.Location == slot {
			curr.Closed = *slot          // Copy value to heap
			curr.Location = &curr.Closed // Point to heap

			if prev == nil {
				vm.openUpvalues = curr.Next
			} else {
				prev.Next = curr.Next
			}
			return
		}
		prev = curr
		curr = curr.Next
	}
}
