(module
  (type (;0;) (func))
  (type (;1;) (func (param i32) (result i32)))
  (type (;2;) (func (param i32 i32 i32)))
  (type (;3;) (func (result i32)))
  (type (;4;) (func (param i32)))
  (func $__wasm_call_ctors (type 0))
  (func $malloc (type 1) (param i32) (result i32)
    (local i32)
    i32.const 0
    i32.const 0
    i32.load offset=1024
    local.tee 1
    local.get 0
    i32.add
    i32.store offset=1024
    local.get 1)
  (func $stack_swap (type 1) (param i32) (result i32)
    local.get 0
    i32.const 24
    i32.shl
    local.get 0
    i32.const 8
    i32.shl
    i32.const 16711680
    i32.and
    i32.or
    local.get 0
    i32.const 8
    i32.shr_u
    i32.const 65280
    i32.and
    local.get 0
    i32.const 24
    i32.shr_u
    i32.or
    i32.or)
  (func $heap_swap (type 2) (param i32 i32 i32)
    local.get 0
    local.get 2
    i32.store
    local.get 1
    local.get 2
    i32.store8 offset=3
    local.get 1
    local.get 0
    i32.load8_u offset=1
    i32.store8 offset=2
    local.get 1
    local.get 0
    i32.load8_u offset=2
    i32.store8 offset=1
    local.get 1
    local.get 0
    i32.load8_u offset=3
    i32.store8)
  (func $start (type 3) (result i32)
    (local i32 i32)
    i32.const 120
    call $dyn_sym_int32
    local.tee 0
    i32.const -272716322
    i32.eq
    sym_assume
    local.get 0
    call $stack_swap
    i32.const -559038737
    i32.eq
    sym_assert
    i32.const 4
    call $malloc
    i32.const 4
    call $malloc
    local.tee 1
    local.get 0
    call $heap_swap
    local.get 1
    i32.load
    i32.const -559038737
    i32.eq
    sym_assert
    i32.const 4)
  (func $dyn_sym_int32 (type 1) (param i32) (result i32)
    local.get 0
    drop
    i32.const 0)
  (func $assume (type 4) (param i32)
    local.get 0
    drop)
  (func $assert (type 4) (param i32)
    local.get 0
    drop)
  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66576))
  (global (;1;) i32 (i32.const 1024))
  (global (;2;) i32 (i32.const 66576))
  (global (;3;) i32 (i32.const 1024))
  (global (;4;) i32 (i32.const 1028))
  (global (;5;) i32 (i32.const 1024))
  (global (;6;) i32 (i32.const 0))
  (global (;7;) i32 (i32.const 1))
  (export "memory" (memory 0))
  (export "__wasm_call_ctors" (func $__wasm_call_ctors))
  (export "malloc" (func $malloc))
  (export "bump_pointer" (global 1))
  (export "stack_swap" (func $stack_swap))
  (export "heap_swap" (func $heap_swap))
  (export "start" (func $start))
  (export "dyn_sym_int32" (func $dyn_sym_int32))
  (export "assume" (func $assume))
  (export "assert" (func $assert))
  (export "__heap_base" (global 2))
  (export "__dso_handle" (global 3))
  (export "__data_end" (global 4))
  (export "__global_base" (global 5))
  (export "__memory_base" (global 6))
  (export "__table_base" (global 7))
  (data (;0;) (i32.const 1024) "\10\04\01\00"))
