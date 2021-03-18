(module
  (type (;0;) (func))
  (type (;1;) (func (param i32) (result i32)))
  (type (;2;) (func (param i32 i32)))
  (type (;3;) (func (result i32)))
  (type (;4;) (func (param i32 i32) (result i32)))
  (type (;5;) (func (param i32)))
  (func $__wasm_call_ctors (type 0))
  (func $f (type 1) (param i32) (result i32)
    (local i32)
    block  ;; label = @1
      local.get 0
      i32.const 1
      i32.and
      br_if 0 (;@1;)
      local.get 0
      i32.const 2
      i32.div_s
      return
    end
    block  ;; label = @1
      local.get 0
      i32.const 3
      i32.div_s
      local.tee 1
      i32.const -3
      i32.mul
      i32.const 0
      local.get 0
      i32.sub
      i32.eq
      br_if 0 (;@1;)
      local.get 0
      i32.const 3
      i32.mul
      i32.const 1
      i32.add
      local.set 1
    end
    local.get 1)
  (func $logic_bomb (type 1) (param i32) (result i32)
    (local i32)
    i32.const 0
    local.set 1
    block  ;; label = @1
      local.get 0
      i32.load8_s
      i32.const 46
      i32.add
      call $f
      local.tee 0
      i32.const 1
      i32.eq
      br_if 0 (;@1;)
      i32.const 24
      local.set 1
      loop  ;; label = @2
        local.get 1
        i32.const -1
        i32.add
        local.set 1
        local.get 0
        call $f
        local.tee 0
        i32.const 1
        i32.ne
        br_if 0 (;@2;)
      end
      i32.const 0
      i32.const 3
      local.get 1
      select
      local.set 1
    end
    local.get 1)
  (func $init_symbolic_string (type 2) (param i32 i32)
    (local i32 i32 i32)
    i32.const 0
    local.set 2
    block  ;; label = @1
      local.get 1
      i32.const 1
      i32.lt_s
      br_if 0 (;@1;)
      i32.const 0
      local.set 2
      loop  ;; label = @2
        local.get 0
        local.get 2
        i32.add
        local.tee 3
        local.get 2
        i32.const 24
        i32.shl
        i32.const 805306368
        i32.add
        i32.const 24
        i32.shr_s
        call $dyn_sym_int32
        local.tee 4
        i32.store8
        local.get 4
        i32.const 24
        i32.shl
        i32.const 0
        i32.gt_s
        call $assume
        local.get 3
        i32.load8_u
        i32.const 127
        i32.ne
        call $assume
        local.get 1
        local.get 2
        i32.const 1
        i32.add
        local.tee 2
        i32.ne
        br_if 0 (;@2;)
      end
      local.get 1
      local.set 2
    end
    local.get 0
    local.get 2
    i32.add
    i32.const 0
    i32.store8)
  (func $__original_main (type 3) (result i32)
    (local i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 0
    global.set 0
    local.get 0
    i32.const 11
    i32.add
    i32.const 4
    call $init_symbolic_string
    local.get 0
    i32.const 11
    i32.add
    call $logic_bomb
    i32.const 3
    i32.eq
    call $assert
    local.get 0
    i32.const 16
    i32.add
    global.set 0
    i32.const 0)
  (func $main (type 4) (param i32 i32) (result i32)
    call $__original_main)
  (func $dyn_sym_int32 (type 1) (param i32) (result i32)
    local.get 0
    drop
    i32.const 0)
  (func $assume (type 5) (param i32)
    local.get 0
    drop)
  (func $assert (type 5) (param i32)
    local.get 0
    drop)
  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66560))
  (global (;1;) i32 (i32.const 1024))
  (global (;2;) i32 (i32.const 1024))
  (global (;3;) i32 (i32.const 1024))
  (global (;4;) i32 (i32.const 66560))
  (global (;5;) i32 (i32.const 0))
  (global (;6;) i32 (i32.const 1))
  (export "memory" (memory 0))
  (export "__wasm_call_ctors" (func $__wasm_call_ctors))
  (export "f" (func $f))
  (export "logic_bomb" (func $logic_bomb))
  (export "init_symbolic_string" (func $init_symbolic_string))
  (export "dyn_sym_int32" (func $dyn_sym_int32))
  (export "assume" (func $assume))
  (export "__original_main" (func $__original_main))
  (export "assert" (func $assert))
  (export "main" (func $main))
  (export "__main_void" (func $__original_main))
  (export "__dso_handle" (global 1))
  (export "__data_end" (global 2))
  (export "__global_base" (global 3))
  (export "__heap_base" (global 4))
  (export "__memory_base" (global 5))
  (export "__table_base" (global 6)))
