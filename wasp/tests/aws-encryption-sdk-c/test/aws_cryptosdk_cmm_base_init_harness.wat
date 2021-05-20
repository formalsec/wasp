(module
  (type (;0;) (func))
  (type (;1;) (func (param i32) (result i32)))
  (type (;2;) (func (param i32 i32)))
  (type (;3;) (func (result i32)))
  (type (;4;) (func (param i32 i32) (result i32)))
  (type (;5;) (func (param i32)))
  (type (;6;) (func (param i32 i32 i32 i32)))
  (type (;7;) (func (param i32) (result f32)))
  (type (;8;) (func (param i32) (result f64)))
  (type (;9;) (func (param i32) (result i64)))
  (func $__wasm_call_ctors (type 0))
  (func $aws_c_string_is_valid (type 1) (param i32) (result i32)
    local.get 0
    i32.const 0
    i32.ne)
  (func $aws_cryptosdk_cmm_vtable_is_valid (type 1) (param i32) (result i32)
    (local i32)
    i32.const 0
    local.set 1
    block  ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      i32.load
      i32.const 20
      i32.ne
      br_if 0 (;@1;)
      local.get 0
      i32.load offset=4
      call $aws_c_string_is_valid
      i32.const 0
      i32.ne
      local.set 1
    end
    local.get 1)
  (func $aws_atomic_var_is_valid_int (type 1) (param i32) (result i32)
    local.get 0
    i32.const 0
    i32.ne)
  (func $aws_atomic_load_int (type 1) (param i32) (result i32)
    local.get 0
    i32.load)
  (func $aws_cryptosdk_cmm_base_is_valid (type 1) (param i32) (result i32)
    (local i32)
    i32.const 0
    local.set 1
    block  ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      call $aws_atomic_var_is_valid_int
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      call $aws_atomic_load_int
      i32.const -1
      i32.add
      i32.const 99999
      i32.gt_u
      br_if 0 (;@1;)
      local.get 0
      i32.load offset=4
      call $aws_cryptosdk_cmm_vtable_is_valid
      i32.const 0
      i32.ne
      local.set 1
    end
    local.get 1)
  (func $aws_atomic_init_int (type 2) (param i32 i32)
    local.get 0
    local.get 1
    i32.store)
  (func $aws_cryptosdk_cmm_base_init (type 2) (param i32 i32)
    local.get 0
    i32.const 0
    i32.ne
    sym_assert
    local.get 1
    call $aws_cryptosdk_cmm_vtable_is_valid
    sym_assert
    local.get 0
    local.get 1
    i32.store offset=4
    local.get 0
    i32.const 1
    call $aws_atomic_init_int
    local.get 0
    call $aws_cryptosdk_cmm_base_is_valid
    sym_assert)
  (func $ensure_c_str_is_allocated (type 1) (param i32) (result i32)
    (local i32 i32 i32 i32)
    i32.const 1024
    call $__VERIFIER_nondet_int
    local.tee 1
    i32.const -1
    i32.add
    local.tee 2
    local.get 1
    i32.lt_u
    local.get 1
    local.get 0
    i32.le_u
    i32.and
    sym_assume
    local.get 1
    call $malloc
    local.set 3
    block  ;; label = @1
      local.get 2
      i32.eqz
      br_if 0 (;@1;)
      local.get 3
      local.set 1
      local.get 2
      local.set 0
      loop  ;; label = @2
        local.get 1
        i32.const 1028
        call $__VERIFIER_nondet_char
        local.tee 4
        i32.const 255
        i32.and
        i32.eqz
        local.get 4
        i32.add
        i32.store8
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        local.get 0
        i32.const -1
        i32.add
        local.tee 0
        br_if 0 (;@2;)
      end
    end
    local.get 3
    local.get 2
    i32.add
    i32.const 0
    i32.store8
    i32.const 1
    sym_assume
    local.get 3)
  (func $ensure_nondet_allocate_cmm_vtable_members (type 2) (param i32 i32)
    block  ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      i32.const 20
      i32.store
      local.get 0
      local.get 1
      call $ensure_c_str_is_allocated
      i32.store offset=4
    end)
  (func $__original_main (type 3) (result i32)
    (local i32)
    global.get 0
    i32.const 32
    i32.sub
    local.tee 0
    global.set 0
    local.get 0
    i32.const 100000
    call $ensure_nondet_allocate_cmm_vtable_members
    local.get 0
    call $aws_cryptosdk_cmm_vtable_is_valid
    sym_assume
    local.get 0
    i32.const 24
    i32.add
    local.get 0
    call $aws_cryptosdk_cmm_base_init
    local.get 0
    i32.const 24
    i32.add
    call $aws_cryptosdk_cmm_base_is_valid
    sym_assert
    local.get 0
    i32.const 32
    i32.add
    global.set 0
    i32.const 0)
  (func $main (type 4) (param i32 i32) (result i32)
    call $__original_main)
  (func $abort (type 0)
    i32.const 0
    sym_assume
    unreachable)
  (func $exit (type 5) (param i32)
    i32.const 1
    sym_assert
    unreachable)
  (func $__assert_fail (type 6) (param i32 i32 i32 i32)
    i32.const 0
    sym_assert)
  (func $__VERIFIER_nondet_bool (type 1) (param i32) (result i32)
    local.get 0
    sym_int
    local.tee 0
    i32.const 2
    i32.lt_u
    sym_assume
    local.get 0)
  (func $__VERIFIER_nondet_char (type 1) (param i32) (result i32)
    local.get 0
    sym_int
    local.tee 0
    i32.const -129
    i32.gt_s
    sym_assume
    local.get 0
    i32.const 128
    i32.lt_s
    sym_assume
    local.get 0
    i32.const 24
    i32.shl
    i32.const 24
    i32.shr_s)
  (func $__VERIFIER_nondet_uchar (type 1) (param i32) (result i32)
    local.get 0
    sym_int
    local.tee 0
    i32.const 256
    i32.lt_u
    sym_assume
    local.get 0
    i32.const 255
    i32.and)
  (func $__VERIFIER_nondet_short (type 1) (param i32) (result i32)
    local.get 0
    sym_int
    local.tee 0
    i32.const 32768
    i32.add
    i32.const 65536
    i32.lt_u
    sym_assume
    local.get 0
    i32.const 16
    i32.shl
    i32.const 16
    i32.shr_s)
  (func $__VERIFIER_nondet_ushort (type 1) (param i32) (result i32)
    local.get 0
    sym_int
    local.tee 0
    i32.const 65536
    i32.lt_u
    sym_assume
    local.get 0
    i32.const 65535
    i32.and)
  (func $__VERIFIER_nondet_int (type 1) (param i32) (result i32)
    local.get 0
    sym_int)
  (func $__VERIFIER_nondet_uint (type 1) (param i32) (result i32)
    local.get 0
    sym_int
    local.set 0
    i32.const 1
    sym_assume
    local.get 0)
  (func $__VERIFIER_nondet_charp (type 1) (param i32) (result i32)
    local.get 0
    sym_int)
  (func $__VERIFIER_nondet_long (type 1) (param i32) (result i32)
    local.get 0
    sym_long
    i32.wrap_i64)
  (func $__VERIFIER_nondet_ulong (type 1) (param i32) (result i32)
    (local i64)
    local.get 0
    sym_long
    local.set 1
    i32.const 1
    sym_assume
    local.get 1
    i32.wrap_i64)
  (func $__VERIFIER_nondet_float (type 7) (param i32) (result f32)
    local.get 0
    sym_float)
  (func $__VERIFIER_nondet_double (type 8) (param i32) (result f64)
    local.get 0
    sym_double)
  (func $assume (type 5) (param i32))
  (func $assert (type 5) (param i32))
  (func $alloc (type 4) (param i32 i32) (result i32)
    local.get 0)
  (func $dealloc (type 5) (param i32))
  (func $is_symbolic (type 4) (param i32 i32) (result i32)
    i32.const 0)
  (func $sym_int (type 1) (param i32) (result i32)
    i32.const 0)
  (func $sym_long (type 9) (param i32) (result i64)
    i64.const 0)
  (func $sym_float (type 7) (param i32) (result f32)
    f32.const 0x0p+0 (;=0;))
  (func $sym_double (type 8) (param i32) (result f64)
    f64.const 0x0p+0 (;=0;))
  (func $malloc (type 1) (param i32) (result i32)
    (local i32 i32)
    i32.const 0
    i32.load offset=1036
    local.set 1
    block  ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      i32.const 0
      local.set 2
      loop  ;; label = @2
        i32.const 0
        i32.load offset=1036
        local.get 2
        i32.add
        i32.const 105
        i32.store8
        local.get 0
        local.get 2
        i32.const 1
        i32.add
        local.tee 2
        i32.ne
        br_if 0 (;@2;)
      end
    end
    i32.const 0
    i32.const 0
    i32.load offset=1036
    local.get 0
    i32.add
    i32.store offset=1036
    local.get 1
    local.get 0
    alloc)
  (func $alloca (type 1) (param i32) (result i32)
    local.get 0
    call $malloc)
  (func $calloc (type 4) (param i32 i32) (result i32)
    (local i32 i32)
    i32.const 0
    i32.load offset=1036
    local.tee 2
    local.set 3
    block  ;; label = @1
      local.get 1
      local.get 0
      i32.mul
      local.tee 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 2
      local.set 3
      i32.const 0
      local.set 1
      loop  ;; label = @2
        local.get 3
        local.get 1
        i32.add
        i32.const 0
        i32.store
        i32.const 0
        i32.load offset=1036
        local.set 3
        local.get 0
        local.get 1
        i32.const 1
        i32.add
        local.tee 1
        i32.ne
        br_if 0 (;@2;)
      end
    end
    i32.const 0
    local.get 3
    local.get 0
    i32.add
    i32.store offset=1036
    local.get 2
    local.get 0
    alloc)
  (func $realloc (type 4) (param i32 i32) (result i32)
    local.get 0
    free
    local.get 0
    local.get 1
    alloc)
  (func $free (type 5) (param i32)
    local.get 0
    free)
  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66576))
  (global (;1;) i32 (i32.const 1036))
  (global (;2;) i32 (i32.const 66576))
  (global (;3;) i32 (i32.const 1024))
  (global (;4;) i32 (i32.const 1040))
  (global (;5;) i32 (i32.const 1024))
  (global (;6;) i32 (i32.const 0))
  (global (;7;) i32 (i32.const 1))
  (export "memory" (memory 0))
  (export "__wasm_call_ctors" (func $__wasm_call_ctors))
  (export "aws_c_string_is_valid" (func $aws_c_string_is_valid))
  (export "aws_cryptosdk_cmm_vtable_is_valid" (func $aws_cryptosdk_cmm_vtable_is_valid))
  (export "aws_atomic_var_is_valid_int" (func $aws_atomic_var_is_valid_int))
  (export "aws_atomic_load_int" (func $aws_atomic_load_int))
  (export "aws_cryptosdk_cmm_base_is_valid" (func $aws_cryptosdk_cmm_base_is_valid))
  (export "aws_atomic_init_int" (func $aws_atomic_init_int))
  (export "aws_cryptosdk_cmm_base_init" (func $aws_cryptosdk_cmm_base_init))
  (export "assert" (func $assert))
  (export "ensure_c_str_is_allocated" (func $ensure_c_str_is_allocated))
  (export "__VERIFIER_nondet_int" (func $__VERIFIER_nondet_int))
  (export "assume" (func $assume))
  (export "malloc" (func $malloc))
  (export "__VERIFIER_nondet_char" (func $__VERIFIER_nondet_char))
  (export "ensure_nondet_allocate_cmm_vtable_members" (func $ensure_nondet_allocate_cmm_vtable_members))
  (export "__original_main" (func $__original_main))
  (export "main" (func $main))
  (export "__main_void" (func $__original_main))
  (export "abort" (func $abort))
  (export "exit" (func $exit))
  (export "__assert_fail" (func $__assert_fail))
  (export "__VERIFIER_nondet_bool" (func $__VERIFIER_nondet_bool))
  (export "sym_int" (func $sym_int))
  (export "__VERIFIER_nondet_uchar" (func $__VERIFIER_nondet_uchar))
  (export "__VERIFIER_nondet_short" (func $__VERIFIER_nondet_short))
  (export "__VERIFIER_nondet_ushort" (func $__VERIFIER_nondet_ushort))
  (export "__VERIFIER_nondet_uint" (func $__VERIFIER_nondet_uint))
  (export "__VERIFIER_nondet_charp" (func $__VERIFIER_nondet_charp))
  (export "__VERIFIER_nondet_long" (func $__VERIFIER_nondet_long))
  (export "sym_long" (func $sym_long))
  (export "__VERIFIER_nondet_ulong" (func $__VERIFIER_nondet_ulong))
  (export "__VERIFIER_nondet_float" (func $__VERIFIER_nondet_float))
  (export "sym_float" (func $sym_float))
  (export "__VERIFIER_nondet_double" (func $__VERIFIER_nondet_double))
  (export "sym_double" (func $sym_double))
  (export "alloc" (func $alloc))
  (export "dealloc" (func $dealloc))
  (export "is_symbolic" (func $is_symbolic))
  (export "bump_pointer" (global 1))
  (export "alloca" (func $alloca))
  (export "calloc" (func $calloc))
  (export "realloc" (func $realloc))
  (export "free" (func $free))
  (export "__heap_base" (global 2))
  (export "__dso_handle" (global 3))
  (export "__data_end" (global 4))
  (export "__global_base" (global 5))
  (export "__memory_base" (global 6))
  (export "__table_base" (global 7))
  (data (;0;) (i32.const 1024) "cap\00str[i]\00")
  (data (;1;) (i32.const 1036) "\10\04\01\00"))
