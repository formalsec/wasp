(module
  (type (;0;) (func))
  (type (;1;) (func (param i32) (result i32)))
  (type (;2;) (func (param i32)))
  (type (;3;) (func (param i32 i32) (result i32)))
  (type (;4;) (func (result i32)))
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
  (func $free (type 2) (param i32))
  (func $makeNode (type 1) (param i32) (result i32)
    (local i32)
    i32.const 12
    call $malloc
    local.tee 1
    i64.const 0
    i64.store offset=4 align=4
    local.get 1
    local.get 0
    i32.store
    local.get 1)
  (func $insert (type 3) (param i32 i32) (result i32)
    (local i32)
    block  ;; label = @1
      local.get 1
      br_if 0 (;@1;)
      local.get 0
      call $makeNode
      return
    end
    block  ;; label = @1
      local.get 1
      i32.load
      local.tee 2
      local.get 0
      i32.le_s
      br_if 0 (;@1;)
      local.get 1
      local.get 0
      local.get 1
      i32.load offset=4
      call $insert
      i32.store offset=4
      local.get 1
      return
    end
    block  ;; label = @1
      local.get 2
      local.get 0
      i32.ge_s
      br_if 0 (;@1;)
      local.get 1
      local.get 0
      local.get 1
      i32.load offset=8
      call $insert
      i32.store offset=8
    end
    local.get 1)
  (func $find (type 3) (param i32 i32) (result i32)
    (local i32 i32)
    block  ;; label = @1
      local.get 1
      br_if 0 (;@1;)
      i32.const 0
      return
    end
    i32.const 1
    local.set 2
    block  ;; label = @1
      local.get 1
      i32.load
      local.tee 3
      local.get 0
      i32.eq
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get 3
        local.get 0
        i32.le_s
        br_if 0 (;@2;)
        local.get 0
        local.get 1
        i32.load offset=4
        call $find
        return
      end
      local.get 0
      local.get 1
      i32.load offset=8
      call $find
      local.set 2
    end
    local.get 2)
  (func $find_min (type 1) (param i32) (result i32)
    (local i32)
    block  ;; label = @1
      local.get 0
      i32.load offset=4
      local.tee 1
      br_if 0 (;@1;)
      local.get 0
      i32.load
      return
    end
    local.get 1
    call $find_min)
  (func $remove (type 3) (param i32 i32) (result i32)
    (local i32)
    block  ;; label = @1
      local.get 1
      br_if 0 (;@1;)
      i32.const 0
      return
    end
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get 1
          i32.load
          local.tee 2
          local.get 0
          i32.ne
          br_if 0 (;@3;)
          local.get 1
          i32.load offset=8
          local.set 2
          block  ;; label = @4
            local.get 1
            i32.load offset=4
            local.tee 0
            br_if 0 (;@4;)
            local.get 2
            return
          end
          local.get 2
          i32.eqz
          br_if 2 (;@1;)
          local.get 2
          call $find_min
          local.tee 0
          local.get 2
          call $remove
          local.set 2
          local.get 1
          local.get 0
          i32.store
          local.get 1
          local.get 2
          i32.store offset=8
          br 1 (;@2;)
        end
        block  ;; label = @3
          local.get 2
          local.get 0
          i32.le_s
          br_if 0 (;@3;)
          local.get 1
          local.get 0
          local.get 1
          i32.load offset=4
          call $remove
          i32.store offset=4
          br 1 (;@2;)
        end
        local.get 1
        local.get 0
        local.get 1
        i32.load offset=8
        call $remove
        i32.store offset=8
      end
      local.get 1
      local.set 0
    end
    local.get 0)
  (func $__original_main (type 4) (result i32)
    (local i32 i32 i32 i32 i32 i32)
    i32.const 97
    call $dynamic_sym_int32
    local.set 0
    i32.const 98
    call $dynamic_sym_int32
    local.set 1
    i32.const 101
    call $dynamic_sym_int32
    local.set 2
    i32.const 102
    call $dynamic_sym_int32
    local.set 3
    local.get 1
    local.get 0
    call $makeNode
    call $insert
    print_memory
    local.set 4
    local.get 2
    local.get 1
    i32.ne
    local.get 2
    local.get 0
    i32.ne
    i32.and
    call $assume
    local.get 3
    local.get 0
    i32.eq
    local.get 3
    local.get 1
    i32.eq
    i32.or
    call $assume
    local.get 2
    local.get 4
    call $find
    local.set 2
    local.get 3
    local.get 4
    call $find
    local.set 3
    local.get 0
    local.get 1
    i32.lt_s
    i32.const 99
    call $dynamic_sym_int32
    local.tee 5
    local.get 0
    i32.gt_s
    i32.and
    call $assume
    local.get 2
    i32.eqz
    local.get 3
    i32.const 0
    i32.ne
    i32.and
    local.get 0
    local.get 1
    local.get 5
    local.get 4
    call $insert
    call $remove
    call $find_min
    i32.eq
    i32.and
    call $assert
    i32.const 0)
  (func $main (type 3) (param i32 i32) (result i32)
    call $__original_main)
  (func $assume (type 2) (param i32)
    local.get 0
    sym_assume)
  (func $assert (type 2) (param i32)
    local.get 0
    sym_assert)
  (func $dynamic_sym_int32 (type 1) (param i32) (result i32)
    local.get 0
    dyn_sym_int32)
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
  (export "free" (func $free))
  (export "makeNode" (func $makeNode))
  (export "insert" (func $insert))
  (export "find" (func $find))
  (export "find_min" (func $find_min))
  (export "remove" (func $remove))
  (export "__original_main" (func $__original_main))
  (export "dynamic_sym_int32" (func $dynamic_sym_int32))
  (export "assume" (func $assume))
  (export "assert" (func $assert))
  (export "main" (func $main))
  (export "__heap_base" (global 2))
  (export "__dso_handle" (global 3))
  (export "__data_end" (global 4))
  (export "__global_base" (global 5))
  (export "__memory_base" (global 6))
  (export "__table_base" (global 7))
  (data (;0;) (i32.const 1024) "\10\04\01\00"))
