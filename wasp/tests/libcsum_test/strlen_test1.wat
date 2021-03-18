(module
  (type (;0;) (func))
  (type (;1;) (func (result i32)))
  (type (;2;) (func (param i32 i32) (result i32)))
  (type (;3;) (func (param i32)))
  (type (;4;) (func (param i32) (result i32)))
  (type (;5;) (func (param i64)))
  (type (;6;) (func (param i32 i32 i32 i32 i32)))
  (type (;7;) (func (param i32 i32 i32 i32)))
  (type (;8;) (func (param i64) (result i64)))
  (type (;9;) (func (param i64 i64) (result i64)))
  (type (;10;) (func (param i32 i32 i32) (result i64)))
  (type (;11;) (func (param i64 i32 i32 i32) (result i64)))
  (type (;12;) (func (param i64) (result i32)))
  (type (;13;) (func (param i32 i32 i32) (result i32)))
  (type (;14;) (func (result i64)))
  (type (;15;) (func (param i32) (result i64)))
  (func $__wasm_call_ctors (type 0))
  (func $__original_main (type 1) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32)
    global.get 0
    local.set 0
    i32.const 32
    local.set 1
    local.get 0
    local.get 1
    i32.sub
    local.set 2
    local.get 2
    global.set 0
    i32.const 0
    local.set 3
    i32.const 32
    local.set 4
    i32.const 24
    local.set 5
    local.get 2
    local.get 5
    i32.add
    local.set 6
    local.get 6
    local.set 7
    i32.const 12
    local.set 8
    local.get 2
    local.get 8
    i32.add
    local.set 9
    local.get 9
    local.set 10
    i32.const 19
    local.set 11
    local.get 2
    local.get 11
    i32.add
    local.set 12
    local.get 12
    local.set 13
    i32.const 4
    local.set 14
    local.get 2
    local.get 3
    i32.store offset=28
    local.get 2
    local.get 14
    i32.store offset=24
    i32.const 4
    local.set 15
    local.get 13
    local.get 15
    i32.add
    local.set 16
    i32.const 0
    local.set 17
    local.get 17
    i32.load8_u offset=1028
    local.set 18
    local.get 16
    local.get 18
    i32.store8
    local.get 17
    i32.load offset=1024 align=1
    local.set 19
    local.get 13
    local.get 19
    i32.store align=1
    local.get 13
    call $strlen
    local.set 20
    local.get 2
    local.get 20
    i32.store offset=12
    local.get 10
    local.get 7
    local.get 4
    call $_solver_EQ
    local.set 21
    local.get 21
    call $summ_print_restriction
    i32.const 32
    local.set 22
    local.get 2
    local.get 22
    i32.add
    local.set 23
    local.get 23
    global.set 0
    local.get 3
    return)
  (func $main (type 2) (param i32 i32) (result i32)
    (local i32)
    call $__original_main
    local.set 2
    local.get 2
    return)
  (func $summ_not_implemented_error (type 3) (param i32)
    (local i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    local.get 0
    i32.store offset=12
    return)
  (func $summ_print_byte (type 3) (param i32)
    (local i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 1029
    local.set 4
    local.get 3
    local.get 0
    i32.store8 offset=15
    local.get 4
    call $summ_not_implemented_error
    i32.const 16
    local.set 5
    local.get 3
    local.get 5
    i32.add
    local.set 6
    local.get 6
    global.set 0
    return)
  (func $summ_maximize (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    i32.const 0
    local.set 5
    i32.const 1045
    local.set 6
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 6
    call $summ_not_implemented_error
    i32.const 16
    local.set 7
    local.get 4
    local.get 7
    i32.add
    local.set 8
    local.get 8
    global.set 0
    local.get 5
    return)
  (func $summ_is_symbolic (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    i32.load offset=12
    local.set 5
    local.get 4
    i32.load offset=8
    local.set 6
    local.get 5
    local.get 6
    call $is_symbolic
    local.set 7
    i32.const 16
    local.set 8
    local.get 4
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 7
    return)
  (func $summ_new_sym_var (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    i32.const 1059
    local.set 5
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 5
    call $summ_not_implemented_error
    i32.const 16
    local.set 6
    local.get 3
    local.get 6
    i32.add
    local.set 7
    local.get 7
    global.set 0
    local.get 4
    return)
  (func $summ_assume (type 5) (param i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    local.get 3
    local.get 0
    i64.store offset=8
    local.get 3
    i64.load offset=8
    local.set 4
    local.get 4
    i32.wrap_i64
    local.set 5
    local.get 5
    call $assume
    i32.const 16
    local.set 6
    local.get 3
    local.get 6
    i32.add
    local.set 7
    local.get 7
    global.set 0
    return)
  (func $_solver_Concat (type 6) (param i32 i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 5
    i32.const 32
    local.set 6
    local.get 5
    local.get 6
    i32.sub
    local.set 7
    local.get 7
    global.set 0
    i32.const 1076
    local.set 8
    local.get 7
    local.get 0
    i32.store offset=28
    local.get 7
    local.get 1
    i32.store offset=24
    local.get 7
    local.get 2
    i32.store offset=20
    local.get 7
    local.get 3
    i32.store offset=16
    local.get 7
    local.get 4
    i32.store offset=12
    local.get 8
    call $summ_not_implemented_error
    i32.const 32
    local.set 9
    local.get 7
    local.get 9
    i32.add
    local.set 10
    local.get 10
    global.set 0
    return)
  (func $_solver_Extract (type 6) (param i32 i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 5
    i32.const 32
    local.set 6
    local.get 5
    local.get 6
    i32.sub
    local.set 7
    local.get 7
    global.set 0
    i32.const 1091
    local.set 8
    local.get 7
    local.get 0
    i32.store offset=28
    local.get 7
    local.get 1
    i32.store offset=24
    local.get 7
    local.get 2
    i32.store offset=20
    local.get 7
    local.get 3
    i32.store offset=16
    local.get 7
    local.get 4
    i32.store offset=12
    local.get 8
    call $summ_not_implemented_error
    i32.const 32
    local.set 9
    local.get 7
    local.get 9
    i32.add
    local.set 10
    local.get 10
    global.set 0
    return)
  (func $_solver_ZeroExt (type 7) (param i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 4
    i32.const 16
    local.set 5
    local.get 4
    local.get 5
    i32.sub
    local.set 6
    local.get 6
    global.set 0
    i32.const 1107
    local.set 7
    local.get 6
    local.get 0
    i32.store offset=12
    local.get 6
    local.get 1
    i32.store offset=8
    local.get 6
    local.get 2
    i32.store offset=4
    local.get 6
    local.get 3
    i32.store
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 6
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    return)
  (func $_solver_SignExt (type 7) (param i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 4
    i32.const 16
    local.set 5
    local.get 4
    local.get 5
    i32.sub
    local.set 6
    local.get 6
    global.set 0
    i32.const 1123
    local.set 7
    local.get 6
    local.get 0
    i32.store offset=12
    local.get 6
    local.get 1
    i32.store offset=8
    local.get 6
    local.get 2
    i32.store offset=4
    local.get 6
    local.get 3
    i32.store
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 6
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    return)
  (func $summ_print_restriction (type 5) (param i64)
    (local i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 1139
    local.set 4
    local.get 3
    local.get 0
    i64.store offset=8
    local.get 4
    call $summ_not_implemented_error
    i32.const 16
    local.set 5
    local.get 3
    local.get 5
    i32.add
    local.set 6
    local.get 6
    global.set 0
    return)
  (func $_solver_NOT (type 8) (param i64) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i64.const 0
    local.set 4
    i32.const 1162
    local.set 5
    local.get 3
    local.get 0
    i64.store offset=8
    local.get 5
    call $summ_not_implemented_error
    i32.const 16
    local.set 6
    local.get 3
    local.get 6
    i32.add
    local.set 7
    local.get 7
    global.set 0
    local.get 4
    return)
  (func $_solver_Or (type 9) (param i64 i64) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    i64.const 0
    local.set 5
    i32.const 1174
    local.set 6
    local.get 4
    local.get 0
    i64.store offset=8
    local.get 4
    local.get 1
    i64.store
    local.get 6
    call $summ_not_implemented_error
    i32.const 16
    local.set 7
    local.get 4
    local.get 7
    i32.add
    local.set 8
    local.get 8
    global.set 0
    local.get 5
    return)
  (func $_solver_And (type 9) (param i64 i64) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    i64.const 0
    local.set 5
    i32.const 1185
    local.set 6
    local.get 4
    local.get 0
    i64.store offset=8
    local.get 4
    local.get 1
    i64.store
    local.get 6
    call $summ_not_implemented_error
    i32.const 16
    local.set 7
    local.get 4
    local.get 7
    i32.add
    local.set 8
    local.get 8
    global.set 0
    local.get 5
    return)
  (func $_solver_EQ (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i64.const 0
    local.set 6
    i32.const 1197
    local.set 7
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 5
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 6
    return)
  (func $_solver_NEQ (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i64.const 0
    local.set 6
    i32.const 1208
    local.set 7
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 5
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 6
    return)
  (func $_solver_LT (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i64.const 0
    local.set 6
    i32.const 1220
    local.set 7
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 5
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 6
    return)
  (func $_solver_LE (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i64.const 0
    local.set 6
    i32.const 1231
    local.set 7
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 5
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 6
    return)
  (func $_solver_SLT (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i64.const 0
    local.set 6
    i32.const 1242
    local.set 7
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 5
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 6
    return)
  (func $_solver_SLE (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i64.const 0
    local.set 6
    i32.const 1254
    local.set 7
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 7
    call $summ_not_implemented_error
    i32.const 16
    local.set 8
    local.get 5
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 6
    return)
  (func $_solver_IF (type 11) (param i64 i32 i32 i32) (result i64)
    (local i32 i32 i32 i64 i32 i32 i32)
    global.get 0
    local.set 4
    i32.const 32
    local.set 5
    local.get 4
    local.get 5
    i32.sub
    local.set 6
    local.get 6
    global.set 0
    i64.const 0
    local.set 7
    i32.const 1266
    local.set 8
    local.get 6
    local.get 0
    i64.store offset=24
    local.get 6
    local.get 1
    i32.store offset=20
    local.get 6
    local.get 2
    i32.store offset=16
    local.get 6
    local.get 3
    i32.store offset=12
    local.get 8
    call $summ_not_implemented_error
    i32.const 32
    local.set 9
    local.get 6
    local.get 9
    i32.add
    local.set 10
    local.get 10
    global.set 0
    local.get 7
    return)
  (func $_solver_is_it_possible (type 12) (param i64) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    i32.const 1277
    local.set 5
    local.get 3
    local.get 0
    i64.store offset=8
    local.get 5
    call $summ_not_implemented_error
    i32.const 16
    local.set 6
    local.get 3
    local.get 6
    i32.add
    local.set 7
    local.get 7
    global.set 0
    local.get 4
    return)
  (func $strlen1 (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    local.get 4
    i32.store offset=8
    loop  ;; label = @1
      i32.const 1
      local.set 5
      i32.const 8
      local.set 6
      local.get 3
      i32.load offset=12
      local.set 7
      local.get 3
      i32.load offset=8
      local.set 8
      local.get 7
      local.get 8
      i32.add
      local.set 9
      local.get 9
      local.get 6
      call $summ_is_symbolic
      local.set 10
      local.get 5
      local.set 11
      block  ;; label = @2
        local.get 10
        br_if 0 (;@2;)
        i32.const 0
        local.set 12
        i32.const 8
        local.set 13
        local.get 3
        i32.load offset=12
        local.set 14
        local.get 3
        i32.load offset=8
        local.set 15
        local.get 14
        local.get 15
        i32.add
        local.set 16
        local.get 16
        local.get 13
        call $summ_is_symbolic
        local.set 17
        local.get 12
        local.set 18
        block  ;; label = @3
          local.get 17
          br_if 0 (;@3;)
          i32.const 0
          local.set 19
          local.get 3
          i32.load offset=12
          local.set 20
          local.get 3
          i32.load offset=8
          local.set 21
          local.get 20
          local.get 21
          i32.add
          local.set 22
          local.get 22
          i32.load8_u
          local.set 23
          i32.const 24
          local.set 24
          local.get 23
          local.get 24
          i32.shl
          local.set 25
          local.get 25
          local.get 24
          i32.shr_s
          local.set 26
          local.get 26
          local.set 27
          local.get 19
          local.set 28
          local.get 27
          local.get 28
          i32.eq
          local.set 29
          local.get 29
          local.set 18
        end
        local.get 18
        local.set 30
        i32.const -1
        local.set 31
        local.get 30
        local.get 31
        i32.xor
        local.set 32
        local.get 32
        local.set 11
      end
      local.get 11
      local.set 33
      i32.const 1
      local.set 34
      local.get 33
      local.get 34
      i32.and
      local.set 35
      block  ;; label = @2
        local.get 35
        i32.eqz
        br_if 0 (;@2;)
        local.get 3
        i32.load offset=8
        local.set 36
        i32.const 1
        local.set 37
        local.get 36
        local.get 37
        i32.add
        local.set 38
        local.get 3
        local.get 38
        i32.store offset=8
        br 1 (;@1;)
      end
    end
    local.get 3
    i32.load offset=8
    local.set 39
    i32.const 16
    local.set 40
    local.get 3
    local.get 40
    i32.add
    local.set 41
    local.get 41
    global.set 0
    local.get 39
    return)
  (func $strlen2 (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    i32.const 0
    local.set 5
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    local.get 5
    i32.store offset=8
    local.get 3
    local.get 4
    i32.store8 offset=7
    block  ;; label = @1
      loop  ;; label = @2
        i32.const 8
        local.set 6
        local.get 3
        i32.load offset=12
        local.set 7
        local.get 3
        i32.load offset=8
        local.set 8
        local.get 7
        local.get 8
        i32.add
        local.set 9
        local.get 9
        local.get 6
        call $summ_is_symbolic
        local.set 10
        block  ;; label = @3
          block  ;; label = @4
            local.get 10
            i32.eqz
            br_if 0 (;@4;)
            i32.const 7
            local.set 11
            local.get 3
            local.get 11
            i32.add
            local.set 12
            local.get 12
            local.set 13
            i32.const 8
            local.set 14
            local.get 3
            i32.load offset=12
            local.set 15
            local.get 3
            i32.load offset=8
            local.set 16
            local.get 15
            local.get 16
            i32.add
            local.set 17
            local.get 17
            local.get 13
            local.get 14
            call $_solver_NEQ
            local.set 18
            local.get 18
            call $_solver_is_it_possible
            local.set 19
            block  ;; label = @5
              local.get 19
              br_if 0 (;@5;)
              br 4 (;@1;)
            end
            i32.const 7
            local.set 20
            local.get 3
            local.get 20
            i32.add
            local.set 21
            local.get 21
            local.set 22
            i32.const 8
            local.set 23
            local.get 3
            i32.load offset=12
            local.set 24
            local.get 3
            i32.load offset=8
            local.set 25
            local.get 24
            local.get 25
            i32.add
            local.set 26
            local.get 26
            local.get 22
            local.get 23
            call $_solver_NEQ
            local.set 27
            local.get 27
            call $summ_assume
            br 1 (;@3;)
          end
          local.get 3
          i32.load offset=12
          local.set 28
          local.get 3
          i32.load offset=8
          local.set 29
          local.get 28
          local.get 29
          i32.add
          local.set 30
          local.get 30
          i32.load8_u
          local.set 31
          i32.const 24
          local.set 32
          local.get 31
          local.get 32
          i32.shl
          local.set 33
          local.get 33
          local.get 32
          i32.shr_s
          local.set 34
          block  ;; label = @4
            local.get 34
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        local.get 3
        i32.load offset=8
        local.set 35
        i32.const 1
        local.set 36
        local.get 35
        local.get 36
        i32.add
        local.set 37
        local.get 3
        local.get 37
        i32.store offset=8
        br 0 (;@2;)
      end
    end
    local.get 3
    i32.load offset=8
    local.set 38
    i32.const 16
    local.set 39
    local.get 3
    local.get 39
    i32.add
    local.set 40
    local.get 40
    global.set 0
    local.get 38
    return)
  (func $strlen (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    i32.load offset=12
    local.set 4
    local.get 4
    call $strlen1
    local.set 5
    i32.const 16
    local.set 6
    local.get 3
    local.get 6
    i32.add
    local.set 7
    local.get 7
    global.set 0
    local.get 5
    return)
  (func $strncmp1 (type 13) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 32
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i32.const 32
    local.set 6
    i32.const 16
    local.set 7
    local.get 5
    local.get 7
    i32.add
    local.set 8
    local.get 8
    local.set 9
    local.get 5
    local.get 0
    i32.store offset=24
    local.get 5
    local.get 1
    i32.store offset=20
    local.get 5
    local.get 2
    i32.store offset=16
    local.get 5
    i32.load offset=24
    local.set 10
    local.get 10
    call $strlen
    local.set 11
    local.get 5
    local.get 11
    i32.store offset=12
    local.get 5
    i32.load offset=20
    local.set 12
    local.get 12
    call $strlen
    local.set 13
    local.get 5
    local.get 13
    i32.store offset=8
    local.get 9
    local.get 6
    call $summ_is_symbolic
    local.set 14
    block  ;; label = @1
      local.get 14
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 15
      i32.const 16
      local.set 16
      local.get 5
      local.get 16
      i32.add
      local.set 17
      local.get 17
      local.set 18
      local.get 18
      local.get 15
      call $summ_maximize
      local.set 19
      local.get 5
      local.get 19
      i32.store offset=16
    end
    local.get 5
    i32.load offset=12
    local.set 20
    local.get 5
    i32.load offset=16
    local.set 21
    local.get 20
    local.set 22
    local.get 21
    local.set 23
    local.get 22
    local.get 23
    i32.lt_s
    local.set 24
    i32.const 1
    local.set 25
    local.get 24
    local.get 25
    i32.and
    local.set 26
    block  ;; label = @1
      block  ;; label = @2
        local.get 26
        i32.eqz
        br_if 0 (;@2;)
        local.get 5
        i32.load offset=12
        local.set 27
        local.get 27
        local.set 28
        br 1 (;@1;)
      end
      local.get 5
      i32.load offset=16
      local.set 29
      local.get 29
      local.set 28
    end
    local.get 28
    local.set 30
    local.get 5
    local.get 30
    i32.store offset=12
    local.get 5
    i32.load offset=8
    local.set 31
    local.get 5
    i32.load offset=16
    local.set 32
    local.get 31
    local.set 33
    local.get 32
    local.set 34
    local.get 33
    local.get 34
    i32.lt_s
    local.set 35
    i32.const 1
    local.set 36
    local.get 35
    local.get 36
    i32.and
    local.set 37
    block  ;; label = @1
      block  ;; label = @2
        local.get 37
        i32.eqz
        br_if 0 (;@2;)
        local.get 5
        i32.load offset=8
        local.set 38
        local.get 38
        local.set 39
        br 1 (;@1;)
      end
      local.get 5
      i32.load offset=16
      local.set 40
      local.get 40
      local.set 39
    end
    local.get 39
    local.set 41
    local.get 5
    local.get 41
    i32.store offset=8
    local.get 5
    i32.load offset=12
    local.set 42
    local.get 5
    i32.load offset=8
    local.set 43
    local.get 42
    local.set 44
    local.get 43
    local.set 45
    local.get 44
    local.get 45
    i32.ne
    local.set 46
    i32.const 1
    local.set 47
    local.get 46
    local.get 47
    i32.and
    local.set 48
    block  ;; label = @1
      block  ;; label = @2
        local.get 48
        i32.eqz
        br_if 0 (;@2;)
        i32.const 1
        local.set 49
        local.get 5
        local.get 49
        i32.store offset=28
        br 1 (;@1;)
      end
      i32.const 0
      local.set 50
      local.get 5
      local.get 50
      i32.store offset=4
      block  ;; label = @2
        loop  ;; label = @3
          local.get 5
          i32.load offset=4
          local.set 51
          local.get 5
          i32.load offset=12
          local.set 52
          local.get 51
          local.set 53
          local.get 52
          local.set 54
          local.get 53
          local.get 54
          i32.lt_s
          local.set 55
          i32.const 1
          local.set 56
          local.get 55
          local.get 56
          i32.and
          local.set 57
          local.get 57
          i32.eqz
          br_if 1 (;@2;)
          i32.const 3
          local.set 58
          local.get 5
          local.get 58
          i32.add
          local.set 59
          local.get 59
          local.set 60
          i32.const 8
          local.set 61
          local.get 5
          i32.load offset=24
          local.set 62
          local.get 5
          i32.load offset=4
          local.set 63
          local.get 62
          local.get 63
          i32.add
          local.set 64
          local.get 64
          i32.load8_u
          local.set 65
          local.get 5
          local.get 65
          i32.store8 offset=3
          local.get 5
          i32.load offset=20
          local.set 66
          local.get 5
          i32.load offset=4
          local.set 67
          local.get 66
          local.get 67
          i32.add
          local.set 68
          local.get 68
          i32.load8_u
          local.set 69
          local.get 5
          local.get 69
          i32.store8 offset=2
          local.get 60
          local.get 61
          call $summ_is_symbolic
          local.set 70
          block  ;; label = @4
            local.get 70
            br_if 0 (;@4;)
            i32.const 2
            local.set 71
            local.get 5
            local.get 71
            i32.add
            local.set 72
            local.get 72
            local.set 73
            i32.const 8
            local.set 74
            local.get 73
            local.get 74
            call $summ_is_symbolic
            local.set 75
            local.get 75
            br_if 0 (;@4;)
            local.get 5
            i32.load8_u offset=3
            local.set 76
            i32.const 24
            local.set 77
            local.get 76
            local.get 77
            i32.shl
            local.set 78
            local.get 78
            local.get 77
            i32.shr_s
            local.set 79
            local.get 5
            i32.load8_u offset=2
            local.set 80
            i32.const 24
            local.set 81
            local.get 80
            local.get 81
            i32.shl
            local.set 82
            local.get 82
            local.get 81
            i32.shr_s
            local.set 83
            local.get 79
            local.set 84
            local.get 83
            local.set 85
            local.get 84
            local.get 85
            i32.ne
            local.set 86
            i32.const 1
            local.set 87
            local.get 86
            local.get 87
            i32.and
            local.set 88
            local.get 88
            i32.eqz
            br_if 0 (;@4;)
            i32.const 1
            local.set 89
            local.get 5
            local.get 89
            i32.store offset=28
            br 3 (;@1;)
          end
          local.get 5
          i32.load offset=4
          local.set 90
          i32.const 1
          local.set 91
          local.get 90
          local.get 91
          i32.add
          local.set 92
          local.get 5
          local.get 92
          i32.store offset=4
          br 0 (;@3;)
        end
      end
      i32.const 0
      local.set 93
      local.get 5
      local.get 93
      i32.store offset=28
    end
    local.get 5
    i32.load offset=28
    local.set 94
    i32.const 32
    local.set 95
    local.get 5
    local.get 95
    i32.add
    local.set 96
    local.get 96
    global.set 0
    local.get 94
    return)
  (func $strncmp2 (type 13) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i64 i32 i32 i32 i64 i32 i32 i32 i64 i64 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i64 i64 i64 i64 i64 i64 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 112
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i32.const 32
    local.set 6
    i32.const 72
    local.set 7
    local.get 5
    local.get 7
    i32.add
    local.set 8
    local.get 8
    local.set 9
    i32.const 0
    local.set 10
    i32.const 1
    local.set 11
    i32.const 0
    local.set 12
    local.get 5
    local.get 0
    i32.store offset=104
    local.get 5
    local.get 1
    i32.store offset=100
    local.get 5
    local.get 2
    i32.store offset=96
    local.get 5
    local.get 12
    i32.store offset=92
    local.get 5
    local.get 11
    i32.store offset=88
    call $summ_true
    local.set 13
    local.get 5
    local.get 13
    i64.store offset=80
    local.get 5
    local.get 10
    i32.store8 offset=79
    local.get 5
    i32.load offset=104
    local.set 14
    local.get 14
    call $strlen
    local.set 15
    local.get 5
    local.get 15
    i32.store offset=72
    local.get 5
    i32.load offset=100
    local.set 16
    local.get 16
    call $strlen
    local.set 17
    local.get 5
    local.get 17
    i32.store offset=68
    local.get 9
    local.get 6
    call $summ_is_symbolic
    local.set 18
    block  ;; label = @1
      local.get 18
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 19
      i32.const 72
      local.set 20
      local.get 5
      local.get 20
      i32.add
      local.set 21
      local.get 21
      local.set 22
      local.get 22
      local.get 19
      call $summ_maximize
      local.set 23
      local.get 5
      local.get 23
      i32.store offset=72
    end
    i32.const 32
    local.set 24
    i32.const 68
    local.set 25
    local.get 5
    local.get 25
    i32.add
    local.set 26
    local.get 26
    local.set 27
    local.get 27
    local.get 24
    call $summ_is_symbolic
    local.set 28
    block  ;; label = @1
      local.get 28
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 29
      i32.const 68
      local.set 30
      local.get 5
      local.get 30
      i32.add
      local.set 31
      local.get 31
      local.set 32
      local.get 32
      local.get 29
      call $summ_maximize
      local.set 33
      local.get 5
      local.get 33
      i32.store offset=68
    end
    i32.const 32
    local.set 34
    i32.const 96
    local.set 35
    local.get 5
    local.get 35
    i32.add
    local.set 36
    local.get 36
    local.set 37
    local.get 37
    local.get 34
    call $summ_is_symbolic
    local.set 38
    block  ;; label = @1
      local.get 38
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 39
      i32.const 96
      local.set 40
      local.get 5
      local.get 40
      i32.add
      local.set 41
      local.get 41
      local.set 42
      local.get 42
      local.get 39
      call $summ_maximize
      local.set 43
      local.get 5
      local.get 43
      i32.store offset=96
    end
    local.get 5
    i32.load offset=72
    local.set 44
    local.get 5
    i32.load offset=96
    local.set 45
    local.get 44
    local.set 46
    local.get 45
    local.set 47
    local.get 46
    local.get 47
    i32.lt_s
    local.set 48
    i32.const 1
    local.set 49
    local.get 48
    local.get 49
    i32.and
    local.set 50
    block  ;; label = @1
      block  ;; label = @2
        local.get 50
        i32.eqz
        br_if 0 (;@2;)
        local.get 5
        i32.load offset=72
        local.set 51
        local.get 51
        local.set 52
        br 1 (;@1;)
      end
      local.get 5
      i32.load offset=96
      local.set 53
      local.get 53
      local.set 52
    end
    local.get 52
    local.set 54
    local.get 5
    local.get 54
    i32.store offset=72
    local.get 5
    i32.load offset=68
    local.set 55
    local.get 5
    i32.load offset=96
    local.set 56
    local.get 55
    local.set 57
    local.get 56
    local.set 58
    local.get 57
    local.get 58
    i32.lt_s
    local.set 59
    i32.const 1
    local.set 60
    local.get 59
    local.get 60
    i32.and
    local.set 61
    block  ;; label = @1
      block  ;; label = @2
        local.get 61
        i32.eqz
        br_if 0 (;@2;)
        local.get 5
        i32.load offset=68
        local.set 62
        local.get 62
        local.set 63
        br 1 (;@1;)
      end
      local.get 5
      i32.load offset=96
      local.set 64
      local.get 64
      local.set 63
    end
    local.get 63
    local.set 65
    local.get 5
    local.get 65
    i32.store offset=68
    local.get 5
    i32.load offset=72
    local.set 66
    local.get 5
    i32.load offset=68
    local.set 67
    local.get 66
    local.set 68
    local.get 67
    local.set 69
    local.get 68
    local.get 69
    i32.lt_s
    local.set 70
    i32.const 1
    local.set 71
    local.get 70
    local.get 71
    i32.and
    local.set 72
    block  ;; label = @1
      block  ;; label = @2
        local.get 72
        i32.eqz
        br_if 0 (;@2;)
        i32.const 8
        local.set 73
        local.get 5
        i32.load offset=100
        local.set 74
        local.get 5
        i32.load offset=72
        local.set 75
        local.get 74
        local.get 75
        i32.add
        local.set 76
        local.get 76
        local.get 73
        call $summ_is_symbolic
        local.set 77
        block  ;; label = @3
          local.get 77
          i32.eqz
          br_if 0 (;@3;)
          i32.const 79
          local.set 78
          local.get 5
          local.get 78
          i32.add
          local.set 79
          local.get 79
          local.set 80
          i32.const 8
          local.set 81
          local.get 5
          i32.load offset=100
          local.set 82
          local.get 5
          i32.load offset=72
          local.set 83
          local.get 82
          local.get 83
          i32.add
          local.set 84
          local.get 84
          local.get 80
          local.get 81
          call $_solver_EQ
          local.set 85
          local.get 85
          call $_solver_is_it_possible
          local.set 86
          local.get 86
          br_if 1 (;@2;)
        end
        i32.const 0
        local.set 87
        i32.const 1
        local.set 88
        local.get 5
        local.get 88
        i32.store offset=92
        local.get 5
        local.get 87
        i32.store offset=88
        br 1 (;@1;)
      end
      local.get 5
      i32.load offset=72
      local.set 89
      local.get 5
      i32.load offset=68
      local.set 90
      local.get 89
      local.set 91
      local.get 90
      local.set 92
      local.get 91
      local.get 92
      i32.gt_s
      local.set 93
      i32.const 1
      local.set 94
      local.get 93
      local.get 94
      i32.and
      local.set 95
      block  ;; label = @2
        block  ;; label = @3
          local.get 95
          i32.eqz
          br_if 0 (;@3;)
          i32.const 8
          local.set 96
          local.get 5
          i32.load offset=104
          local.set 97
          local.get 5
          i32.load offset=68
          local.set 98
          local.get 97
          local.get 98
          i32.add
          local.set 99
          local.get 99
          local.get 96
          call $summ_is_symbolic
          local.set 100
          block  ;; label = @4
            local.get 100
            i32.eqz
            br_if 0 (;@4;)
            i32.const 79
            local.set 101
            local.get 5
            local.get 101
            i32.add
            local.set 102
            local.get 102
            local.set 103
            i32.const 8
            local.set 104
            local.get 5
            i32.load offset=104
            local.set 105
            local.get 5
            i32.load offset=68
            local.set 106
            local.get 105
            local.get 106
            i32.add
            local.set 107
            local.get 107
            local.get 103
            local.get 104
            call $_solver_EQ
            local.set 108
            local.get 108
            call $_solver_is_it_possible
            local.set 109
            local.get 109
            br_if 1 (;@3;)
          end
          i32.const 0
          local.set 110
          i32.const 1
          local.set 111
          local.get 5
          local.get 111
          i32.store offset=92
          local.get 5
          local.get 110
          i32.store offset=88
          br 1 (;@2;)
        end
        local.get 5
        i32.load offset=72
        local.set 112
        local.get 5
        i32.load offset=68
        local.set 113
        local.get 112
        local.set 114
        local.get 113
        local.set 115
        local.get 114
        local.get 115
        i32.lt_s
        local.set 116
        i32.const 1
        local.set 117
        local.get 116
        local.get 117
        i32.and
        local.set 118
        block  ;; label = @3
          block  ;; label = @4
            local.get 118
            i32.eqz
            br_if 0 (;@4;)
            local.get 5
            i32.load offset=72
            local.set 119
            local.get 119
            local.set 120
            br 1 (;@3;)
          end
          local.get 5
          i32.load offset=68
          local.set 121
          local.get 121
          local.set 120
        end
        local.get 120
        local.set 122
        i32.const 0
        local.set 123
        local.get 5
        local.get 122
        i32.store offset=64
        local.get 5
        local.get 123
        i32.store offset=60
        block  ;; label = @3
          loop  ;; label = @4
            local.get 5
            i32.load offset=60
            local.set 124
            local.get 5
            i32.load offset=64
            local.set 125
            local.get 124
            local.set 126
            local.get 125
            local.set 127
            local.get 126
            local.get 127
            i32.lt_s
            local.set 128
            i32.const 1
            local.set 129
            local.get 128
            local.get 129
            i32.and
            local.set 130
            local.get 130
            i32.eqz
            br_if 1 (;@3;)
            i32.const 8
            local.set 131
            local.get 5
            i32.load offset=104
            local.set 132
            local.get 5
            i32.load offset=60
            local.set 133
            local.get 132
            local.get 133
            i32.add
            local.set 134
            local.get 134
            i32.load8_u
            local.set 135
            local.get 5
            local.get 135
            i32.store8 offset=59
            local.get 5
            i32.load offset=100
            local.set 136
            local.get 5
            i32.load offset=60
            local.set 137
            local.get 136
            local.get 137
            i32.add
            local.set 138
            local.get 138
            i32.load8_u
            local.set 139
            local.get 5
            local.get 139
            i32.store8 offset=58
            local.get 5
            i32.load offset=104
            local.set 140
            local.get 5
            i32.load offset=60
            local.set 141
            local.get 140
            local.get 141
            i32.add
            local.set 142
            local.get 142
            local.get 131
            call $summ_is_symbolic
            local.set 143
            block  ;; label = @5
              local.get 143
              br_if 0 (;@5;)
              i32.const 8
              local.set 144
              local.get 5
              i32.load offset=100
              local.set 145
              local.get 5
              i32.load offset=60
              local.set 146
              local.get 145
              local.get 146
              i32.add
              local.set 147
              local.get 147
              local.get 144
              call $summ_is_symbolic
              local.set 148
              local.get 148
              br_if 0 (;@5;)
              local.get 5
              i32.load8_u offset=59
              local.set 149
              i32.const 24
              local.set 150
              local.get 149
              local.get 150
              i32.shl
              local.set 151
              local.get 151
              local.get 150
              i32.shr_s
              local.set 152
              local.get 5
              i32.load8_u offset=58
              local.set 153
              i32.const 24
              local.set 154
              local.get 153
              local.get 154
              i32.shl
              local.set 155
              local.get 155
              local.get 154
              i32.shr_s
              local.set 156
              local.get 152
              local.set 157
              local.get 156
              local.set 158
              local.get 157
              local.get 158
              i32.ne
              local.set 159
              i32.const 1
              local.set 160
              local.get 159
              local.get 160
              i32.and
              local.set 161
              local.get 161
              i32.eqz
              br_if 0 (;@5;)
              i32.const 1
              local.set 162
              i32.const 0
              local.set 163
              local.get 5
              local.get 163
              i32.store offset=88
              local.get 5
              local.get 162
              i32.store offset=92
              br 2 (;@3;)
            end
            i32.const 59
            local.set 164
            local.get 5
            local.get 164
            i32.add
            local.set 165
            local.get 165
            local.set 166
            i32.const 58
            local.set 167
            local.get 5
            local.get 167
            i32.add
            local.set 168
            local.get 168
            local.set 169
            i32.const 8
            local.set 170
            local.get 166
            local.get 169
            local.get 170
            call $_solver_EQ
            local.set 171
            local.get 5
            local.get 171
            i64.store offset=48
            local.get 166
            local.get 169
            local.get 170
            call $_solver_NEQ
            local.set 172
            local.get 5
            local.get 172
            i64.store offset=40
            local.get 5
            i64.load offset=48
            local.set 173
            local.get 173
            call $_solver_is_it_possible
            local.set 174
            block  ;; label = @5
              block  ;; label = @6
                local.get 174
                br_if 0 (;@6;)
                i32.const 1
                local.set 175
                i32.const 0
                local.set 176
                local.get 5
                local.get 176
                i32.store offset=88
                local.get 5
                local.get 175
                i32.store offset=92
                br 1 (;@5;)
              end
              local.get 5
              i64.load offset=40
              local.set 177
              local.get 177
              call $_solver_is_it_possible
              local.set 178
              block  ;; label = @6
                local.get 178
                i32.eqz
                br_if 0 (;@6;)
                i32.const 1
                local.set 179
                local.get 5
                local.get 179
                i32.store offset=92
              end
              i32.const 1
              local.set 180
              local.get 5
              local.get 180
              i32.store offset=88
              local.get 5
              i64.load offset=80
              local.set 181
              local.get 5
              i64.load offset=48
              local.set 182
              local.get 181
              local.get 182
              call $_solver_And
              local.set 183
              local.get 5
              local.get 183
              i64.store offset=80
            end
            local.get 5
            i32.load offset=60
            local.set 184
            i32.const 1
            local.set 185
            local.get 184
            local.get 185
            i32.add
            local.set 186
            local.get 5
            local.get 186
            i32.store offset=60
            br 0 (;@4;)
          end
        end
      end
    end
    local.get 5
    i32.load offset=92
    local.set 187
    block  ;; label = @1
      block  ;; label = @2
        local.get 187
        i32.eqz
        br_if 0 (;@2;)
        local.get 5
        i32.load offset=88
        local.set 188
        local.get 188
        i32.eqz
        br_if 0 (;@2;)
        i32.const 32
        local.set 189
        i32.const 28
        local.set 190
        local.get 5
        local.get 190
        i32.add
        local.set 191
        local.get 191
        local.set 192
        i32.const 36
        local.set 193
        local.get 5
        local.get 193
        i32.add
        local.set 194
        local.get 194
        local.set 195
        i32.const 32
        local.set 196
        local.get 5
        local.get 196
        i32.add
        local.set 197
        local.get 197
        local.set 198
        i32.const 1
        local.set 199
        i32.const 0
        local.set 200
        local.get 189
        call $summ_new_sym_var
        local.set 201
        local.get 5
        local.get 201
        i32.store offset=36
        local.get 5
        local.get 200
        i32.store offset=32
        local.get 5
        local.get 199
        i32.store offset=28
        local.get 195
        local.get 198
        local.get 189
        call $_solver_EQ
        local.set 202
        local.get 5
        local.get 202
        i64.store offset=16
        local.get 195
        local.get 192
        local.get 189
        call $_solver_EQ
        local.set 203
        local.get 5
        local.get 203
        i64.store offset=8
        local.get 5
        i64.load offset=80
        local.set 204
        local.get 5
        i64.load offset=16
        local.set 205
        local.get 204
        local.get 205
        call $_solver_And
        local.set 206
        local.get 5
        local.get 206
        i64.store offset=80
        local.get 5
        i64.load offset=80
        local.set 207
        local.get 5
        i64.load offset=8
        local.set 208
        local.get 207
        local.get 208
        call $_solver_Or
        local.set 209
        local.get 5
        local.get 209
        i64.store offset=80
        local.get 5
        i64.load offset=80
        local.set 210
        local.get 210
        call $summ_assume
        local.get 5
        i32.load offset=36
        local.set 211
        local.get 5
        local.get 211
        i32.store offset=108
        br 1 (;@1;)
      end
      local.get 5
      i32.load offset=92
      local.set 212
      block  ;; label = @2
        local.get 212
        i32.eqz
        br_if 0 (;@2;)
        i32.const 1
        local.set 213
        local.get 5
        local.get 213
        i32.store offset=108
        br 1 (;@1;)
      end
      local.get 5
      i32.load offset=88
      local.set 214
      block  ;; label = @2
        local.get 214
        i32.eqz
        br_if 0 (;@2;)
        i32.const 0
        local.set 215
        local.get 5
        local.get 215
        i32.store offset=108
        br 1 (;@1;)
      end
      i32.const -1
      local.set 216
      local.get 5
      local.get 216
      i32.store offset=108
    end
    local.get 5
    i32.load offset=108
    local.set 217
    i32.const 112
    local.set 218
    local.get 5
    local.get 218
    i32.add
    local.set 219
    local.get 219
    global.set 0
    local.get 217
    return)
  (func $strncmp (type 13) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 5
    i32.load offset=12
    local.set 6
    local.get 5
    i32.load offset=8
    local.set 7
    local.get 5
    i32.load offset=4
    local.set 8
    local.get 6
    local.get 7
    local.get 8
    call $strncmp2
    local.set 9
    i32.const 16
    local.set 10
    local.get 5
    local.get 10
    i32.add
    local.set 11
    local.get 11
    global.set 0
    local.get 9
    return)
  (func $strcmp1 (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 32
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    local.get 4
    local.get 0
    i32.store offset=24
    local.get 4
    local.get 1
    i32.store offset=20
    local.get 4
    i32.load offset=24
    local.set 5
    local.get 5
    call $strlen
    local.set 6
    local.get 4
    local.get 6
    i32.store offset=16
    local.get 4
    i32.load offset=20
    local.set 7
    local.get 7
    call $strlen
    local.set 8
    local.get 4
    local.get 8
    i32.store offset=12
    local.get 4
    i32.load offset=16
    local.set 9
    local.get 4
    i32.load offset=12
    local.set 10
    local.get 9
    local.set 11
    local.get 10
    local.set 12
    local.get 11
    local.get 12
    i32.ne
    local.set 13
    i32.const 1
    local.set 14
    local.get 13
    local.get 14
    i32.and
    local.set 15
    block  ;; label = @1
      block  ;; label = @2
        local.get 15
        i32.eqz
        br_if 0 (;@2;)
        i32.const 1
        local.set 16
        local.get 4
        local.get 16
        i32.store offset=28
        br 1 (;@1;)
      end
      i32.const 0
      local.set 17
      local.get 4
      local.get 17
      i32.store offset=8
      block  ;; label = @2
        loop  ;; label = @3
          local.get 4
          i32.load offset=8
          local.set 18
          local.get 4
          i32.load offset=16
          local.set 19
          local.get 18
          local.set 20
          local.get 19
          local.set 21
          local.get 20
          local.get 21
          i32.lt_s
          local.set 22
          i32.const 1
          local.set 23
          local.get 22
          local.get 23
          i32.and
          local.set 24
          local.get 24
          i32.eqz
          br_if 1 (;@2;)
          i32.const 7
          local.set 25
          local.get 4
          local.get 25
          i32.add
          local.set 26
          local.get 26
          local.set 27
          i32.const 8
          local.set 28
          local.get 4
          i32.load offset=24
          local.set 29
          local.get 4
          i32.load offset=8
          local.set 30
          local.get 29
          local.get 30
          i32.add
          local.set 31
          local.get 31
          i32.load8_u
          local.set 32
          local.get 4
          local.get 32
          i32.store8 offset=7
          local.get 4
          i32.load offset=20
          local.set 33
          local.get 4
          i32.load offset=8
          local.set 34
          local.get 33
          local.get 34
          i32.add
          local.set 35
          local.get 35
          i32.load8_u
          local.set 36
          local.get 4
          local.get 36
          i32.store8 offset=6
          local.get 27
          local.get 28
          call $summ_is_symbolic
          local.set 37
          block  ;; label = @4
            local.get 37
            br_if 0 (;@4;)
            i32.const 6
            local.set 38
            local.get 4
            local.get 38
            i32.add
            local.set 39
            local.get 39
            local.set 40
            i32.const 8
            local.set 41
            local.get 40
            local.get 41
            call $summ_is_symbolic
            local.set 42
            local.get 42
            br_if 0 (;@4;)
            local.get 4
            i32.load8_u offset=7
            local.set 43
            i32.const 24
            local.set 44
            local.get 43
            local.get 44
            i32.shl
            local.set 45
            local.get 45
            local.get 44
            i32.shr_s
            local.set 46
            local.get 4
            i32.load8_u offset=6
            local.set 47
            i32.const 24
            local.set 48
            local.get 47
            local.get 48
            i32.shl
            local.set 49
            local.get 49
            local.get 48
            i32.shr_s
            local.set 50
            local.get 46
            local.set 51
            local.get 50
            local.set 52
            local.get 51
            local.get 52
            i32.ne
            local.set 53
            i32.const 1
            local.set 54
            local.get 53
            local.get 54
            i32.and
            local.set 55
            local.get 55
            i32.eqz
            br_if 0 (;@4;)
            i32.const 1
            local.set 56
            local.get 4
            local.get 56
            i32.store offset=28
            br 3 (;@1;)
          end
          local.get 4
          i32.load offset=8
          local.set 57
          i32.const 1
          local.set 58
          local.get 57
          local.get 58
          i32.add
          local.set 59
          local.get 4
          local.get 59
          i32.store offset=8
          br 0 (;@3;)
        end
      end
      i32.const 0
      local.set 60
      local.get 4
      local.get 60
      i32.store offset=28
    end
    local.get 4
    i32.load offset=28
    local.set 61
    i32.const 32
    local.set 62
    local.get 4
    local.get 62
    i32.add
    local.set 63
    local.get 63
    global.set 0
    local.get 61
    return)
  (func $strcmp2 (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i64 i32 i32 i32 i64 i32 i32 i32 i64 i64 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i64 i64 i64 i64 i64 i64 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 112
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    i32.const 32
    local.set 5
    i32.const 72
    local.set 6
    local.get 4
    local.get 6
    i32.add
    local.set 7
    local.get 7
    local.set 8
    i32.const 0
    local.set 9
    i32.const 1
    local.set 10
    i32.const 0
    local.set 11
    local.get 4
    local.get 0
    i32.store offset=104
    local.get 4
    local.get 1
    i32.store offset=100
    local.get 4
    local.get 11
    i32.store offset=96
    local.get 4
    local.get 10
    i32.store offset=92
    call $summ_true
    local.set 12
    local.get 4
    local.get 12
    i64.store offset=80
    local.get 4
    local.get 9
    i32.store8 offset=79
    local.get 4
    i32.load offset=104
    local.set 13
    local.get 13
    call $strlen
    local.set 14
    local.get 4
    local.get 14
    i32.store offset=72
    local.get 4
    i32.load offset=100
    local.set 15
    local.get 15
    call $strlen
    local.set 16
    local.get 4
    local.get 16
    i32.store offset=68
    local.get 8
    local.get 5
    call $summ_is_symbolic
    local.set 17
    block  ;; label = @1
      local.get 17
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 18
      i32.const 72
      local.set 19
      local.get 4
      local.get 19
      i32.add
      local.set 20
      local.get 20
      local.set 21
      local.get 21
      local.get 18
      call $summ_maximize
      local.set 22
      local.get 4
      local.get 22
      i32.store offset=72
    end
    i32.const 32
    local.set 23
    i32.const 68
    local.set 24
    local.get 4
    local.get 24
    i32.add
    local.set 25
    local.get 25
    local.set 26
    local.get 26
    local.get 23
    call $summ_is_symbolic
    local.set 27
    block  ;; label = @1
      local.get 27
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 28
      i32.const 68
      local.set 29
      local.get 4
      local.get 29
      i32.add
      local.set 30
      local.get 30
      local.set 31
      local.get 31
      local.get 28
      call $summ_maximize
      local.set 32
      local.get 4
      local.get 32
      i32.store offset=68
    end
    local.get 4
    i32.load offset=72
    local.set 33
    local.get 4
    i32.load offset=68
    local.set 34
    local.get 33
    local.set 35
    local.get 34
    local.set 36
    local.get 35
    local.get 36
    i32.lt_s
    local.set 37
    i32.const 1
    local.set 38
    local.get 37
    local.get 38
    i32.and
    local.set 39
    block  ;; label = @1
      block  ;; label = @2
        local.get 39
        i32.eqz
        br_if 0 (;@2;)
        i32.const 8
        local.set 40
        local.get 4
        i32.load offset=100
        local.set 41
        local.get 4
        i32.load offset=72
        local.set 42
        local.get 41
        local.get 42
        i32.add
        local.set 43
        local.get 43
        local.get 40
        call $summ_is_symbolic
        local.set 44
        block  ;; label = @3
          local.get 44
          i32.eqz
          br_if 0 (;@3;)
          i32.const 79
          local.set 45
          local.get 4
          local.get 45
          i32.add
          local.set 46
          local.get 46
          local.set 47
          i32.const 8
          local.set 48
          local.get 4
          i32.load offset=100
          local.set 49
          local.get 4
          i32.load offset=72
          local.set 50
          local.get 49
          local.get 50
          i32.add
          local.set 51
          local.get 51
          local.get 47
          local.get 48
          call $_solver_EQ
          local.set 52
          local.get 52
          call $_solver_is_it_possible
          local.set 53
          local.get 53
          br_if 1 (;@2;)
        end
        i32.const 0
        local.set 54
        i32.const 1
        local.set 55
        local.get 4
        local.get 55
        i32.store offset=96
        local.get 4
        local.get 54
        i32.store offset=92
        br 1 (;@1;)
      end
      local.get 4
      i32.load offset=72
      local.set 56
      local.get 4
      i32.load offset=68
      local.set 57
      local.get 56
      local.set 58
      local.get 57
      local.set 59
      local.get 58
      local.get 59
      i32.gt_s
      local.set 60
      i32.const 1
      local.set 61
      local.get 60
      local.get 61
      i32.and
      local.set 62
      block  ;; label = @2
        block  ;; label = @3
          local.get 62
          i32.eqz
          br_if 0 (;@3;)
          i32.const 8
          local.set 63
          local.get 4
          i32.load offset=104
          local.set 64
          local.get 4
          i32.load offset=68
          local.set 65
          local.get 64
          local.get 65
          i32.add
          local.set 66
          local.get 66
          local.get 63
          call $summ_is_symbolic
          local.set 67
          block  ;; label = @4
            local.get 67
            i32.eqz
            br_if 0 (;@4;)
            i32.const 79
            local.set 68
            local.get 4
            local.get 68
            i32.add
            local.set 69
            local.get 69
            local.set 70
            i32.const 8
            local.set 71
            local.get 4
            i32.load offset=104
            local.set 72
            local.get 4
            i32.load offset=68
            local.set 73
            local.get 72
            local.get 73
            i32.add
            local.set 74
            local.get 74
            local.get 70
            local.get 71
            call $_solver_EQ
            local.set 75
            local.get 75
            call $_solver_is_it_possible
            local.set 76
            local.get 76
            br_if 1 (;@3;)
          end
          i32.const 0
          local.set 77
          i32.const 1
          local.set 78
          local.get 4
          local.get 78
          i32.store offset=96
          local.get 4
          local.get 77
          i32.store offset=92
          br 1 (;@2;)
        end
        local.get 4
        i32.load offset=72
        local.set 79
        local.get 4
        i32.load offset=68
        local.set 80
        local.get 79
        local.set 81
        local.get 80
        local.set 82
        local.get 81
        local.get 82
        i32.lt_s
        local.set 83
        i32.const 1
        local.set 84
        local.get 83
        local.get 84
        i32.and
        local.set 85
        block  ;; label = @3
          block  ;; label = @4
            local.get 85
            i32.eqz
            br_if 0 (;@4;)
            local.get 4
            i32.load offset=72
            local.set 86
            local.get 86
            local.set 87
            br 1 (;@3;)
          end
          local.get 4
          i32.load offset=68
          local.set 88
          local.get 88
          local.set 87
        end
        local.get 87
        local.set 89
        i32.const 0
        local.set 90
        local.get 4
        local.get 89
        i32.store offset=64
        local.get 4
        local.get 90
        i32.store offset=60
        block  ;; label = @3
          loop  ;; label = @4
            local.get 4
            i32.load offset=60
            local.set 91
            local.get 4
            i32.load offset=64
            local.set 92
            local.get 91
            local.set 93
            local.get 92
            local.set 94
            local.get 93
            local.get 94
            i32.lt_s
            local.set 95
            i32.const 1
            local.set 96
            local.get 95
            local.get 96
            i32.and
            local.set 97
            local.get 97
            i32.eqz
            br_if 1 (;@3;)
            i32.const 8
            local.set 98
            local.get 4
            i32.load offset=104
            local.set 99
            local.get 4
            i32.load offset=60
            local.set 100
            local.get 99
            local.get 100
            i32.add
            local.set 101
            local.get 101
            i32.load8_u
            local.set 102
            local.get 4
            local.get 102
            i32.store8 offset=59
            local.get 4
            i32.load offset=100
            local.set 103
            local.get 4
            i32.load offset=60
            local.set 104
            local.get 103
            local.get 104
            i32.add
            local.set 105
            local.get 105
            i32.load8_u
            local.set 106
            local.get 4
            local.get 106
            i32.store8 offset=58
            local.get 4
            i32.load offset=104
            local.set 107
            local.get 4
            i32.load offset=60
            local.set 108
            local.get 107
            local.get 108
            i32.add
            local.set 109
            local.get 109
            local.get 98
            call $summ_is_symbolic
            local.set 110
            block  ;; label = @5
              local.get 110
              br_if 0 (;@5;)
              i32.const 8
              local.set 111
              local.get 4
              i32.load offset=100
              local.set 112
              local.get 4
              i32.load offset=60
              local.set 113
              local.get 112
              local.get 113
              i32.add
              local.set 114
              local.get 114
              local.get 111
              call $summ_is_symbolic
              local.set 115
              local.get 115
              br_if 0 (;@5;)
              local.get 4
              i32.load8_u offset=59
              local.set 116
              i32.const 24
              local.set 117
              local.get 116
              local.get 117
              i32.shl
              local.set 118
              local.get 118
              local.get 117
              i32.shr_s
              local.set 119
              local.get 4
              i32.load8_u offset=58
              local.set 120
              i32.const 24
              local.set 121
              local.get 120
              local.get 121
              i32.shl
              local.set 122
              local.get 122
              local.get 121
              i32.shr_s
              local.set 123
              local.get 119
              local.set 124
              local.get 123
              local.set 125
              local.get 124
              local.get 125
              i32.ne
              local.set 126
              i32.const 1
              local.set 127
              local.get 126
              local.get 127
              i32.and
              local.set 128
              local.get 128
              i32.eqz
              br_if 0 (;@5;)
              i32.const 1
              local.set 129
              i32.const 0
              local.set 130
              local.get 4
              local.get 130
              i32.store offset=92
              local.get 4
              local.get 129
              i32.store offset=96
              br 2 (;@3;)
            end
            i32.const 59
            local.set 131
            local.get 4
            local.get 131
            i32.add
            local.set 132
            local.get 132
            local.set 133
            i32.const 58
            local.set 134
            local.get 4
            local.get 134
            i32.add
            local.set 135
            local.get 135
            local.set 136
            i32.const 8
            local.set 137
            local.get 133
            local.get 136
            local.get 137
            call $_solver_EQ
            local.set 138
            local.get 4
            local.get 138
            i64.store offset=48
            local.get 133
            local.get 136
            local.get 137
            call $_solver_NEQ
            local.set 139
            local.get 4
            local.get 139
            i64.store offset=40
            local.get 4
            i64.load offset=48
            local.set 140
            local.get 140
            call $_solver_is_it_possible
            local.set 141
            block  ;; label = @5
              block  ;; label = @6
                local.get 141
                br_if 0 (;@6;)
                i32.const 1
                local.set 142
                i32.const 0
                local.set 143
                local.get 4
                local.get 143
                i32.store offset=92
                local.get 4
                local.get 142
                i32.store offset=96
                br 1 (;@5;)
              end
              local.get 4
              i64.load offset=40
              local.set 144
              local.get 144
              call $_solver_is_it_possible
              local.set 145
              block  ;; label = @6
                local.get 145
                i32.eqz
                br_if 0 (;@6;)
                i32.const 1
                local.set 146
                local.get 4
                local.get 146
                i32.store offset=96
              end
              i32.const 1
              local.set 147
              local.get 4
              local.get 147
              i32.store offset=92
              local.get 4
              i64.load offset=80
              local.set 148
              local.get 4
              i64.load offset=48
              local.set 149
              local.get 148
              local.get 149
              call $_solver_And
              local.set 150
              local.get 4
              local.get 150
              i64.store offset=80
            end
            local.get 4
            i32.load offset=60
            local.set 151
            i32.const 1
            local.set 152
            local.get 151
            local.get 152
            i32.add
            local.set 153
            local.get 4
            local.get 153
            i32.store offset=60
            br 0 (;@4;)
          end
        end
      end
    end
    local.get 4
    i32.load offset=96
    local.set 154
    block  ;; label = @1
      block  ;; label = @2
        local.get 154
        i32.eqz
        br_if 0 (;@2;)
        local.get 4
        i32.load offset=92
        local.set 155
        local.get 155
        i32.eqz
        br_if 0 (;@2;)
        i32.const 32
        local.set 156
        i32.const 28
        local.set 157
        local.get 4
        local.get 157
        i32.add
        local.set 158
        local.get 158
        local.set 159
        i32.const 36
        local.set 160
        local.get 4
        local.get 160
        i32.add
        local.set 161
        local.get 161
        local.set 162
        i32.const 32
        local.set 163
        local.get 4
        local.get 163
        i32.add
        local.set 164
        local.get 164
        local.set 165
        i32.const 1
        local.set 166
        i32.const 0
        local.set 167
        local.get 156
        call $summ_new_sym_var
        local.set 168
        local.get 4
        local.get 168
        i32.store offset=36
        local.get 4
        local.get 167
        i32.store offset=32
        local.get 4
        local.get 166
        i32.store offset=28
        local.get 162
        local.get 165
        local.get 156
        call $_solver_EQ
        local.set 169
        local.get 4
        local.get 169
        i64.store offset=16
        local.get 162
        local.get 159
        local.get 156
        call $_solver_EQ
        local.set 170
        local.get 4
        local.get 170
        i64.store offset=8
        local.get 4
        i64.load offset=80
        local.set 171
        local.get 4
        i64.load offset=16
        local.set 172
        local.get 171
        local.get 172
        call $_solver_And
        local.set 173
        local.get 4
        local.get 173
        i64.store offset=80
        local.get 4
        i64.load offset=80
        local.set 174
        local.get 4
        i64.load offset=8
        local.set 175
        local.get 174
        local.get 175
        call $_solver_Or
        local.set 176
        local.get 4
        local.get 176
        i64.store offset=80
        local.get 4
        i64.load offset=80
        local.set 177
        local.get 177
        call $summ_assume
        local.get 4
        i32.load offset=36
        local.set 178
        local.get 4
        local.get 178
        i32.store offset=108
        br 1 (;@1;)
      end
      local.get 4
      i32.load offset=96
      local.set 179
      block  ;; label = @2
        local.get 179
        i32.eqz
        br_if 0 (;@2;)
        i32.const 1
        local.set 180
        local.get 4
        local.get 180
        i32.store offset=108
        br 1 (;@1;)
      end
      local.get 4
      i32.load offset=92
      local.set 181
      block  ;; label = @2
        local.get 181
        i32.eqz
        br_if 0 (;@2;)
        i32.const 0
        local.set 182
        local.get 4
        local.get 182
        i32.store offset=108
        br 1 (;@1;)
      end
      i32.const -1
      local.set 183
      local.get 4
      local.get 183
      i32.store offset=108
    end
    local.get 4
    i32.load offset=108
    local.set 184
    i32.const 112
    local.set 185
    local.get 4
    local.get 185
    i32.add
    local.set 186
    local.get 186
    global.set 0
    local.get 184
    return)
  (func $strcmp (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    i32.load offset=12
    local.set 5
    local.get 4
    i32.load offset=8
    local.set 6
    local.get 5
    local.get 6
    call $strcmp2
    local.set 7
    i32.const 16
    local.set 8
    local.get 4
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 7
    return)
  (func $strcpy1 (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    i32.const 0
    local.set 5
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    local.get 5
    i32.store offset=4
    loop  ;; label = @1
      i32.const 1
      local.set 6
      i32.const 8
      local.set 7
      local.get 4
      i32.load offset=8
      local.set 8
      local.get 4
      i32.load offset=4
      local.set 9
      local.get 8
      local.get 9
      i32.add
      local.set 10
      local.get 10
      local.get 7
      call $summ_is_symbolic
      local.set 11
      local.get 6
      local.set 12
      block  ;; label = @2
        local.get 11
        br_if 0 (;@2;)
        i32.const 0
        local.set 13
        i32.const 8
        local.set 14
        local.get 4
        i32.load offset=8
        local.set 15
        local.get 4
        i32.load offset=4
        local.set 16
        local.get 15
        local.get 16
        i32.add
        local.set 17
        local.get 17
        local.get 14
        call $summ_is_symbolic
        local.set 18
        local.get 13
        local.set 19
        block  ;; label = @3
          local.get 18
          br_if 0 (;@3;)
          i32.const 0
          local.set 20
          local.get 4
          i32.load offset=8
          local.set 21
          local.get 4
          i32.load offset=4
          local.set 22
          local.get 21
          local.get 22
          i32.add
          local.set 23
          local.get 23
          i32.load8_u
          local.set 24
          i32.const 24
          local.set 25
          local.get 24
          local.get 25
          i32.shl
          local.set 26
          local.get 26
          local.get 25
          i32.shr_s
          local.set 27
          local.get 27
          local.set 28
          local.get 20
          local.set 29
          local.get 28
          local.get 29
          i32.eq
          local.set 30
          local.get 30
          local.set 19
        end
        local.get 19
        local.set 31
        i32.const -1
        local.set 32
        local.get 31
        local.get 32
        i32.xor
        local.set 33
        local.get 33
        local.set 12
      end
      local.get 12
      local.set 34
      i32.const 1
      local.set 35
      local.get 34
      local.get 35
      i32.and
      local.set 36
      block  ;; label = @2
        local.get 36
        i32.eqz
        br_if 0 (;@2;)
        local.get 4
        i32.load offset=8
        local.set 37
        local.get 4
        i32.load offset=4
        local.set 38
        local.get 37
        local.get 38
        i32.add
        local.set 39
        local.get 39
        i32.load8_u
        local.set 40
        local.get 4
        i32.load offset=12
        local.set 41
        local.get 4
        i32.load offset=4
        local.set 42
        local.get 41
        local.get 42
        i32.add
        local.set 43
        local.get 43
        local.get 40
        i32.store8
        local.get 4
        i32.load offset=4
        local.set 44
        i32.const 1
        local.set 45
        local.get 44
        local.get 45
        i32.add
        local.set 46
        local.get 4
        local.get 46
        i32.store offset=4
        br 1 (;@1;)
      end
    end
    i32.const 0
    local.set 47
    local.get 4
    i32.load offset=12
    local.set 48
    local.get 4
    i32.load offset=4
    local.set 49
    local.get 48
    local.get 49
    i32.add
    local.set 50
    local.get 50
    local.get 47
    i32.store8
    local.get 4
    i32.load offset=12
    local.set 51
    i32.const 16
    local.set 52
    local.get 4
    local.get 52
    i32.add
    local.set 53
    local.get 53
    global.set 0
    local.get 51
    return)
  (func $strcpy2 (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    i32.const 0
    local.set 5
    i32.const 0
    local.set 6
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    local.get 6
    i32.store offset=4
    local.get 4
    local.get 5
    i32.store8 offset=3
    block  ;; label = @1
      loop  ;; label = @2
        i32.const 8
        local.set 7
        local.get 4
        i32.load offset=8
        local.set 8
        local.get 4
        i32.load offset=4
        local.set 9
        local.get 8
        local.get 9
        i32.add
        local.set 10
        local.get 10
        local.get 7
        call $summ_is_symbolic
        local.set 11
        block  ;; label = @3
          block  ;; label = @4
            local.get 11
            i32.eqz
            br_if 0 (;@4;)
            i32.const 3
            local.set 12
            local.get 4
            local.get 12
            i32.add
            local.set 13
            local.get 13
            local.set 14
            i32.const 8
            local.set 15
            local.get 4
            i32.load offset=8
            local.set 16
            local.get 4
            i32.load offset=4
            local.set 17
            local.get 16
            local.get 17
            i32.add
            local.set 18
            local.get 18
            local.get 14
            local.get 15
            call $_solver_NEQ
            local.set 19
            local.get 19
            call $_solver_is_it_possible
            local.set 20
            block  ;; label = @5
              local.get 20
              br_if 0 (;@5;)
              br 4 (;@1;)
            end
            i32.const 3
            local.set 21
            local.get 4
            local.get 21
            i32.add
            local.set 22
            local.get 22
            local.set 23
            i32.const 8
            local.set 24
            local.get 4
            i32.load offset=8
            local.set 25
            local.get 4
            i32.load offset=4
            local.set 26
            local.get 25
            local.get 26
            i32.add
            local.set 27
            local.get 27
            local.get 23
            local.get 24
            call $_solver_NEQ
            local.set 28
            local.get 28
            call $summ_assume
            br 1 (;@3;)
          end
          local.get 4
          i32.load offset=8
          local.set 29
          local.get 4
          i32.load offset=4
          local.set 30
          local.get 29
          local.get 30
          i32.add
          local.set 31
          local.get 31
          i32.load8_u
          local.set 32
          i32.const 24
          local.set 33
          local.get 32
          local.get 33
          i32.shl
          local.set 34
          local.get 34
          local.get 33
          i32.shr_s
          local.set 35
          block  ;; label = @4
            local.get 35
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        local.get 4
        i32.load offset=8
        local.set 36
        local.get 4
        i32.load offset=4
        local.set 37
        local.get 36
        local.get 37
        i32.add
        local.set 38
        local.get 38
        i32.load8_u
        local.set 39
        local.get 4
        i32.load offset=12
        local.set 40
        local.get 4
        i32.load offset=4
        local.set 41
        local.get 40
        local.get 41
        i32.add
        local.set 42
        local.get 42
        local.get 39
        i32.store8
        local.get 4
        i32.load offset=4
        local.set 43
        i32.const 1
        local.set 44
        local.get 43
        local.get 44
        i32.add
        local.set 45
        local.get 4
        local.get 45
        i32.store offset=4
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 46
    local.get 4
    i32.load offset=12
    local.set 47
    local.get 4
    i32.load offset=4
    local.set 48
    local.get 47
    local.get 48
    i32.add
    local.set 49
    local.get 49
    local.get 46
    i32.store8
    local.get 4
    i32.load offset=12
    local.set 50
    i32.const 16
    local.set 51
    local.get 4
    local.get 51
    i32.add
    local.set 52
    local.get 52
    global.set 0
    local.get 50
    return)
  (func $strcpy (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    i32.load offset=12
    local.set 5
    local.get 4
    i32.load offset=8
    local.set 6
    local.get 5
    local.get 6
    call $strcpy2
    local.set 7
    i32.const 16
    local.set 8
    local.get 4
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 7
    return)
  (func $strncpy1 (type 13) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i32.const 32
    local.set 6
    i32.const 4
    local.set 7
    local.get 5
    local.get 7
    i32.add
    local.set 8
    local.get 8
    local.set 9
    i32.const 0
    local.set 10
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 5
    local.get 10
    i32.store
    local.get 9
    local.get 6
    call $summ_is_symbolic
    local.set 11
    block  ;; label = @1
      local.get 11
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 12
      i32.const 4
      local.set 13
      local.get 5
      local.get 13
      i32.add
      local.set 14
      local.get 14
      local.set 15
      local.get 15
      local.get 12
      call $summ_maximize
      local.set 16
      local.get 5
      local.get 16
      i32.store offset=4
    end
    block  ;; label = @1
      loop  ;; label = @2
        local.get 5
        i32.load
        local.set 17
        local.get 5
        i32.load offset=4
        local.set 18
        local.get 17
        local.set 19
        local.get 18
        local.set 20
        local.get 19
        local.get 20
        i32.lt_s
        local.set 21
        i32.const 1
        local.set 22
        local.get 21
        local.get 22
        i32.and
        local.set 23
        local.get 23
        i32.eqz
        br_if 1 (;@1;)
        i32.const 8
        local.set 24
        local.get 5
        i32.load offset=8
        local.set 25
        local.get 5
        i32.load
        local.set 26
        local.get 25
        local.get 26
        i32.add
        local.set 27
        local.get 27
        local.get 24
        call $summ_is_symbolic
        local.set 28
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get 28
              br_if 0 (;@5;)
              i32.const 8
              local.set 29
              local.get 5
              i32.load offset=8
              local.set 30
              local.get 5
              i32.load
              local.set 31
              local.get 30
              local.get 31
              i32.add
              local.set 32
              local.get 32
              local.get 29
              call $summ_is_symbolic
              local.set 33
              local.get 33
              br_if 0 (;@5;)
              local.get 5
              i32.load offset=8
              local.set 34
              local.get 5
              i32.load
              local.set 35
              local.get 34
              local.get 35
              i32.add
              local.set 36
              local.get 36
              i32.load8_u
              local.set 37
              i32.const 24
              local.set 38
              local.get 37
              local.get 38
              i32.shl
              local.set 39
              local.get 39
              local.get 38
              i32.shr_s
              local.set 40
              local.get 40
              i32.eqz
              br_if 1 (;@4;)
            end
            local.get 5
            i32.load offset=8
            local.set 41
            local.get 5
            i32.load
            local.set 42
            local.get 41
            local.get 42
            i32.add
            local.set 43
            local.get 43
            i32.load8_u
            local.set 44
            local.get 5
            i32.load offset=12
            local.set 45
            local.get 5
            i32.load
            local.set 46
            local.get 45
            local.get 46
            i32.add
            local.set 47
            local.get 47
            local.get 44
            i32.store8
            local.get 5
            i32.load
            local.set 48
            i32.const 1
            local.set 49
            local.get 48
            local.get 49
            i32.add
            local.set 50
            local.get 5
            local.get 50
            i32.store
            br 1 (;@3;)
          end
          br 2 (;@1;)
        end
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 51
    local.get 5
    i32.load offset=12
    local.set 52
    local.get 5
    i32.load
    local.set 53
    local.get 52
    local.get 53
    i32.add
    local.set 54
    local.get 54
    local.get 51
    i32.store8
    local.get 5
    i32.load offset=12
    local.set 55
    i32.const 16
    local.set 56
    local.get 5
    local.get 56
    i32.add
    local.set 57
    local.get 57
    global.set 0
    local.get 55
    return)
  (func $strncpy2 (type 13) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 32
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i32.const 32
    local.set 6
    i32.const 20
    local.set 7
    local.get 5
    local.get 7
    i32.add
    local.set 8
    local.get 8
    local.set 9
    i32.const 0
    local.set 10
    i32.const 0
    local.set 11
    local.get 5
    local.get 0
    i32.store offset=28
    local.get 5
    local.get 1
    i32.store offset=24
    local.get 5
    local.get 2
    i32.store offset=20
    local.get 5
    local.get 11
    i32.store offset=16
    local.get 5
    local.get 10
    i32.store8 offset=15
    local.get 9
    local.get 6
    call $summ_is_symbolic
    local.set 12
    block  ;; label = @1
      local.get 12
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 13
      i32.const 20
      local.set 14
      local.get 5
      local.get 14
      i32.add
      local.set 15
      local.get 15
      local.set 16
      local.get 16
      local.get 13
      call $summ_maximize
      local.set 17
      local.get 5
      local.get 17
      i32.store offset=20
    end
    block  ;; label = @1
      loop  ;; label = @2
        local.get 5
        i32.load offset=16
        local.set 18
        local.get 5
        i32.load offset=20
        local.set 19
        local.get 18
        local.set 20
        local.get 19
        local.set 21
        local.get 20
        local.get 21
        i32.lt_s
        local.set 22
        i32.const 1
        local.set 23
        local.get 22
        local.get 23
        i32.and
        local.set 24
        local.get 24
        i32.eqz
        br_if 1 (;@1;)
        i32.const 8
        local.set 25
        local.get 5
        i32.load offset=24
        local.set 26
        local.get 5
        i32.load offset=16
        local.set 27
        local.get 26
        local.get 27
        i32.add
        local.set 28
        local.get 28
        local.get 25
        call $summ_is_symbolic
        local.set 29
        block  ;; label = @3
          block  ;; label = @4
            local.get 29
            i32.eqz
            br_if 0 (;@4;)
            i32.const 15
            local.set 30
            local.get 5
            local.get 30
            i32.add
            local.set 31
            local.get 31
            local.set 32
            i32.const 8
            local.set 33
            local.get 5
            i32.load offset=24
            local.set 34
            local.get 5
            i32.load offset=16
            local.set 35
            local.get 34
            local.get 35
            i32.add
            local.set 36
            local.get 36
            local.get 32
            local.get 33
            call $_solver_NEQ
            local.set 37
            local.get 37
            call $_solver_is_it_possible
            local.set 38
            block  ;; label = @5
              local.get 38
              br_if 0 (;@5;)
              br 4 (;@1;)
            end
            i32.const 15
            local.set 39
            local.get 5
            local.get 39
            i32.add
            local.set 40
            local.get 40
            local.set 41
            i32.const 8
            local.set 42
            local.get 5
            i32.load offset=24
            local.set 43
            local.get 5
            i32.load offset=16
            local.set 44
            local.get 43
            local.get 44
            i32.add
            local.set 45
            local.get 45
            local.get 41
            local.get 42
            call $_solver_NEQ
            local.set 46
            local.get 46
            call $summ_assume
            br 1 (;@3;)
          end
          local.get 5
          i32.load offset=24
          local.set 47
          local.get 5
          i32.load offset=16
          local.set 48
          local.get 47
          local.get 48
          i32.add
          local.set 49
          local.get 49
          i32.load8_u
          local.set 50
          i32.const 24
          local.set 51
          local.get 50
          local.get 51
          i32.shl
          local.set 52
          local.get 52
          local.get 51
          i32.shr_s
          local.set 53
          block  ;; label = @4
            local.get 53
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        local.get 5
        i32.load offset=24
        local.set 54
        local.get 5
        i32.load offset=16
        local.set 55
        local.get 54
        local.get 55
        i32.add
        local.set 56
        local.get 56
        i32.load8_u
        local.set 57
        local.get 5
        i32.load offset=28
        local.set 58
        local.get 5
        i32.load offset=16
        local.set 59
        local.get 58
        local.get 59
        i32.add
        local.set 60
        local.get 60
        local.get 57
        i32.store8
        local.get 5
        i32.load offset=16
        local.set 61
        i32.const 1
        local.set 62
        local.get 61
        local.get 62
        i32.add
        local.set 63
        local.get 5
        local.get 63
        i32.store offset=16
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 64
    local.get 5
    i32.load offset=28
    local.set 65
    local.get 5
    i32.load offset=16
    local.set 66
    local.get 65
    local.get 66
    i32.add
    local.set 67
    local.get 67
    local.get 64
    i32.store8
    local.get 5
    i32.load offset=28
    local.set 68
    i32.const 32
    local.set 69
    local.get 5
    local.get 69
    i32.add
    local.set 70
    local.get 70
    global.set 0
    local.get 68
    return)
  (func $strncpy (type 13) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 5
    i32.load offset=12
    local.set 6
    local.get 5
    i32.load offset=8
    local.set 7
    local.get 5
    i32.load offset=4
    local.set 8
    local.get 6
    local.get 7
    local.get 8
    call $strncpy2
    local.set 9
    i32.const 16
    local.set 10
    local.get 5
    local.get 10
    i32.add
    local.set 11
    local.get 11
    global.set 0
    local.get 9
    return)
  (func $strcat1 (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    i32.load offset=12
    local.set 5
    local.get 5
    call $strlen
    local.set 6
    local.get 4
    local.get 6
    i32.store offset=4
    loop  ;; label = @1
      i32.const 1
      local.set 7
      i32.const 8
      local.set 8
      local.get 4
      i32.load offset=8
      local.set 9
      local.get 4
      i32.load offset=4
      local.set 10
      local.get 9
      local.get 10
      i32.add
      local.set 11
      local.get 11
      local.get 8
      call $summ_is_symbolic
      local.set 12
      local.get 7
      local.set 13
      block  ;; label = @2
        local.get 12
        br_if 0 (;@2;)
        i32.const 0
        local.set 14
        i32.const 8
        local.set 15
        local.get 4
        i32.load offset=8
        local.set 16
        local.get 4
        i32.load offset=4
        local.set 17
        local.get 16
        local.get 17
        i32.add
        local.set 18
        local.get 18
        local.get 15
        call $summ_is_symbolic
        local.set 19
        local.get 14
        local.set 20
        block  ;; label = @3
          local.get 19
          br_if 0 (;@3;)
          i32.const 0
          local.set 21
          local.get 4
          i32.load offset=8
          local.set 22
          local.get 4
          i32.load offset=4
          local.set 23
          local.get 22
          local.get 23
          i32.add
          local.set 24
          local.get 24
          i32.load8_u
          local.set 25
          i32.const 24
          local.set 26
          local.get 25
          local.get 26
          i32.shl
          local.set 27
          local.get 27
          local.get 26
          i32.shr_s
          local.set 28
          local.get 28
          local.set 29
          local.get 21
          local.set 30
          local.get 29
          local.get 30
          i32.eq
          local.set 31
          local.get 31
          local.set 20
        end
        local.get 20
        local.set 32
        i32.const -1
        local.set 33
        local.get 32
        local.get 33
        i32.xor
        local.set 34
        local.get 34
        local.set 13
      end
      local.get 13
      local.set 35
      i32.const 1
      local.set 36
      local.get 35
      local.get 36
      i32.and
      local.set 37
      block  ;; label = @2
        local.get 37
        i32.eqz
        br_if 0 (;@2;)
        local.get 4
        i32.load offset=8
        local.set 38
        local.get 4
        i32.load offset=4
        local.set 39
        local.get 38
        local.get 39
        i32.add
        local.set 40
        local.get 40
        i32.load8_u
        local.set 41
        local.get 4
        i32.load offset=12
        local.set 42
        local.get 4
        i32.load offset=4
        local.set 43
        local.get 42
        local.get 43
        i32.add
        local.set 44
        local.get 44
        local.get 41
        i32.store8
        local.get 4
        i32.load offset=4
        local.set 45
        i32.const 1
        local.set 46
        local.get 45
        local.get 46
        i32.add
        local.set 47
        local.get 4
        local.get 47
        i32.store offset=4
        br 1 (;@1;)
      end
    end
    i32.const 0
    local.set 48
    local.get 4
    i32.load offset=12
    local.set 49
    local.get 4
    i32.load offset=4
    local.set 50
    local.get 49
    local.get 50
    i32.add
    local.set 51
    local.get 51
    local.get 48
    i32.store8
    local.get 4
    i32.load offset=12
    local.set 52
    i32.const 16
    local.set 53
    local.get 4
    local.get 53
    i32.add
    local.set 54
    local.get 54
    global.set 0
    local.get 52
    return)
  (func $strcat2 (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 32
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    i32.const 0
    local.set 5
    i32.const 0
    local.set 6
    local.get 4
    local.get 0
    i32.store offset=28
    local.get 4
    local.get 1
    i32.store offset=24
    local.get 4
    i32.load offset=28
    local.set 7
    local.get 7
    call $strlen
    local.set 8
    local.get 4
    local.get 8
    i32.store offset=20
    local.get 4
    local.get 6
    i32.store offset=16
    local.get 4
    local.get 5
    i32.store8 offset=15
    block  ;; label = @1
      loop  ;; label = @2
        i32.const 8
        local.set 9
        local.get 4
        i32.load offset=24
        local.set 10
        local.get 4
        i32.load offset=16
        local.set 11
        local.get 10
        local.get 11
        i32.add
        local.set 12
        local.get 12
        local.get 9
        call $summ_is_symbolic
        local.set 13
        block  ;; label = @3
          block  ;; label = @4
            local.get 13
            i32.eqz
            br_if 0 (;@4;)
            i32.const 15
            local.set 14
            local.get 4
            local.get 14
            i32.add
            local.set 15
            local.get 15
            local.set 16
            i32.const 8
            local.set 17
            local.get 4
            i32.load offset=24
            local.set 18
            local.get 4
            i32.load offset=16
            local.set 19
            local.get 18
            local.get 19
            i32.add
            local.set 20
            local.get 20
            local.get 16
            local.get 17
            call $_solver_NEQ
            local.set 21
            local.get 21
            call $_solver_is_it_possible
            local.set 22
            block  ;; label = @5
              local.get 22
              br_if 0 (;@5;)
              br 4 (;@1;)
            end
            i32.const 15
            local.set 23
            local.get 4
            local.get 23
            i32.add
            local.set 24
            local.get 24
            local.set 25
            i32.const 8
            local.set 26
            local.get 4
            i32.load offset=24
            local.set 27
            local.get 4
            i32.load offset=16
            local.set 28
            local.get 27
            local.get 28
            i32.add
            local.set 29
            local.get 29
            local.get 25
            local.get 26
            call $_solver_NEQ
            local.set 30
            local.get 30
            call $summ_assume
            br 1 (;@3;)
          end
          local.get 4
          i32.load offset=24
          local.set 31
          local.get 4
          i32.load offset=16
          local.set 32
          local.get 31
          local.get 32
          i32.add
          local.set 33
          local.get 33
          i32.load8_u
          local.set 34
          i32.const 24
          local.set 35
          local.get 34
          local.get 35
          i32.shl
          local.set 36
          local.get 36
          local.get 35
          i32.shr_s
          local.set 37
          block  ;; label = @4
            local.get 37
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        local.get 4
        i32.load offset=24
        local.set 38
        local.get 4
        i32.load offset=16
        local.set 39
        local.get 38
        local.get 39
        i32.add
        local.set 40
        local.get 40
        i32.load8_u
        local.set 41
        local.get 4
        i32.load offset=28
        local.set 42
        local.get 4
        i32.load offset=20
        local.set 43
        local.get 42
        local.get 43
        i32.add
        local.set 44
        local.get 44
        local.get 41
        i32.store8
        local.get 4
        i32.load offset=20
        local.set 45
        i32.const 1
        local.set 46
        local.get 45
        local.get 46
        i32.add
        local.set 47
        local.get 4
        local.get 47
        i32.store offset=20
        local.get 4
        i32.load offset=16
        local.set 48
        i32.const 1
        local.set 49
        local.get 48
        local.get 49
        i32.add
        local.set 50
        local.get 4
        local.get 50
        i32.store offset=16
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 51
    local.get 4
    i32.load offset=28
    local.set 52
    local.get 4
    i32.load offset=20
    local.set 53
    local.get 52
    local.get 53
    i32.add
    local.set 54
    local.get 54
    local.get 51
    i32.store8
    local.get 4
    i32.load offset=28
    local.set 55
    i32.const 32
    local.set 56
    local.get 4
    local.get 56
    i32.add
    local.set 57
    local.get 57
    global.set 0
    local.get 55
    return)
  (func $strcat (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    local.get 4
    global.set 0
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    i32.load offset=12
    local.set 5
    local.get 4
    i32.load offset=8
    local.set 6
    local.get 5
    local.get 6
    call $strcat2
    local.set 7
    i32.const 16
    local.set 8
    local.get 4
    local.get 8
    i32.add
    local.set 9
    local.get 9
    global.set 0
    local.get 7
    return)
  (func $puts1 (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    local.get 4
    i32.store offset=8
    loop  ;; label = @1
      i32.const 1
      local.set 5
      i32.const 8
      local.set 6
      local.get 3
      i32.load offset=12
      local.set 7
      local.get 3
      i32.load offset=8
      local.set 8
      local.get 7
      local.get 8
      i32.add
      local.set 9
      local.get 9
      local.get 6
      call $summ_is_symbolic
      local.set 10
      local.get 5
      local.set 11
      block  ;; label = @2
        local.get 10
        br_if 0 (;@2;)
        i32.const 0
        local.set 12
        i32.const 8
        local.set 13
        local.get 3
        i32.load offset=12
        local.set 14
        local.get 3
        i32.load offset=8
        local.set 15
        local.get 14
        local.get 15
        i32.add
        local.set 16
        local.get 16
        local.get 13
        call $summ_is_symbolic
        local.set 17
        local.get 12
        local.set 18
        block  ;; label = @3
          local.get 17
          br_if 0 (;@3;)
          i32.const 0
          local.set 19
          local.get 3
          i32.load offset=12
          local.set 20
          local.get 3
          i32.load offset=8
          local.set 21
          local.get 20
          local.get 21
          i32.add
          local.set 22
          local.get 22
          i32.load8_u
          local.set 23
          i32.const 24
          local.set 24
          local.get 23
          local.get 24
          i32.shl
          local.set 25
          local.get 25
          local.get 24
          i32.shr_s
          local.set 26
          local.get 26
          local.set 27
          local.get 19
          local.set 28
          local.get 27
          local.get 28
          i32.eq
          local.set 29
          local.get 29
          local.set 18
        end
        local.get 18
        local.set 30
        i32.const -1
        local.set 31
        local.get 30
        local.get 31
        i32.xor
        local.set 32
        local.get 32
        local.set 11
      end
      local.get 11
      local.set 33
      i32.const 1
      local.set 34
      local.get 33
      local.get 34
      i32.and
      local.set 35
      block  ;; label = @2
        local.get 35
        i32.eqz
        br_if 0 (;@2;)
        local.get 3
        i32.load offset=12
        local.set 36
        local.get 3
        i32.load offset=8
        local.set 37
        local.get 36
        local.get 37
        i32.add
        local.set 38
        local.get 38
        i32.load8_u
        local.set 39
        i32.const 24
        local.set 40
        local.get 39
        local.get 40
        i32.shl
        local.set 41
        local.get 41
        local.get 40
        i32.shr_s
        local.set 42
        local.get 42
        call $summ_print_byte
        local.get 3
        i32.load offset=8
        local.set 43
        i32.const 1
        local.set 44
        local.get 43
        local.get 44
        i32.add
        local.set 45
        local.get 3
        local.get 45
        i32.store offset=8
        br 1 (;@1;)
      end
    end
    i32.const 10
    local.set 46
    i32.const 24
    local.set 47
    local.get 46
    local.get 47
    i32.shl
    local.set 48
    local.get 48
    local.get 47
    i32.shr_s
    local.set 49
    local.get 49
    call $summ_print_byte
    local.get 3
    i32.load offset=8
    local.set 50
    i32.const 16
    local.set 51
    local.get 3
    local.get 51
    i32.add
    local.set 52
    local.get 52
    global.set 0
    local.get 50
    return)
  (func $puts2 (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    i32.const 0
    local.set 5
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    local.get 5
    i32.store offset=8
    local.get 3
    local.get 4
    i32.store8 offset=7
    block  ;; label = @1
      loop  ;; label = @2
        i32.const 8
        local.set 6
        local.get 3
        i32.load offset=12
        local.set 7
        local.get 3
        i32.load offset=8
        local.set 8
        local.get 7
        local.get 8
        i32.add
        local.set 9
        local.get 9
        local.get 6
        call $summ_is_symbolic
        local.set 10
        block  ;; label = @3
          block  ;; label = @4
            local.get 10
            i32.eqz
            br_if 0 (;@4;)
            i32.const 7
            local.set 11
            local.get 3
            local.get 11
            i32.add
            local.set 12
            local.get 12
            local.set 13
            i32.const 8
            local.set 14
            local.get 3
            i32.load offset=12
            local.set 15
            local.get 3
            i32.load offset=8
            local.set 16
            local.get 15
            local.get 16
            i32.add
            local.set 17
            local.get 17
            local.get 13
            local.get 14
            call $_solver_NEQ
            local.set 18
            local.get 18
            call $_solver_is_it_possible
            local.set 19
            block  ;; label = @5
              local.get 19
              br_if 0 (;@5;)
              br 4 (;@1;)
            end
            i32.const 7
            local.set 20
            local.get 3
            local.get 20
            i32.add
            local.set 21
            local.get 21
            local.set 22
            i32.const 8
            local.set 23
            local.get 3
            i32.load offset=12
            local.set 24
            local.get 3
            i32.load offset=8
            local.set 25
            local.get 24
            local.get 25
            i32.add
            local.set 26
            local.get 26
            local.get 22
            local.get 23
            call $_solver_NEQ
            local.set 27
            local.get 27
            call $summ_assume
            br 1 (;@3;)
          end
          local.get 3
          i32.load offset=12
          local.set 28
          local.get 3
          i32.load offset=8
          local.set 29
          local.get 28
          local.get 29
          i32.add
          local.set 30
          local.get 30
          i32.load8_u
          local.set 31
          i32.const 24
          local.set 32
          local.get 31
          local.get 32
          i32.shl
          local.set 33
          local.get 33
          local.get 32
          i32.shr_s
          local.set 34
          block  ;; label = @4
            local.get 34
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        local.get 3
        i32.load offset=12
        local.set 35
        local.get 3
        i32.load offset=8
        local.set 36
        local.get 35
        local.get 36
        i32.add
        local.set 37
        local.get 37
        i32.load8_u
        local.set 38
        i32.const 24
        local.set 39
        local.get 38
        local.get 39
        i32.shl
        local.set 40
        local.get 40
        local.get 39
        i32.shr_s
        local.set 41
        local.get 41
        call $summ_print_byte
        local.get 3
        i32.load offset=8
        local.set 42
        i32.const 1
        local.set 43
        local.get 42
        local.get 43
        i32.add
        local.set 44
        local.get 3
        local.get 44
        i32.store offset=8
        br 0 (;@2;)
      end
    end
    i32.const 10
    local.set 45
    i32.const 24
    local.set 46
    local.get 45
    local.get 46
    i32.shl
    local.set 47
    local.get 47
    local.get 46
    i32.shr_s
    local.set 48
    local.get 48
    call $summ_print_byte
    local.get 3
    i32.load offset=8
    local.set 49
    i32.const 16
    local.set 50
    local.get 3
    local.get 50
    i32.add
    local.set 51
    local.get 51
    global.set 0
    local.get 49
    return)
  (func $puts (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    i32.load offset=12
    local.set 4
    local.get 4
    call $puts2
    local.set 5
    i32.const 16
    local.set 6
    local.get 3
    local.get 6
    i32.add
    local.set 7
    local.get 7
    global.set 0
    local.get 5
    return)
  (func $putchar (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    i32.load offset=12
    local.set 4
    i32.const 24
    local.set 5
    local.get 4
    local.get 5
    i32.shl
    local.set 6
    local.get 6
    local.get 5
    i32.shr_s
    local.set 7
    local.get 7
    call $summ_print_byte
    local.get 3
    i32.load offset=12
    local.set 8
    i32.const 16
    local.set 9
    local.get 3
    local.get 9
    i32.add
    local.set 10
    local.get 10
    global.set 0
    local.get 8
    return)
  (func $getchar (type 1) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 0
    i32.const 16
    local.set 1
    local.get 0
    local.get 1
    i32.sub
    local.set 2
    local.get 2
    global.set 0
    i32.const 8
    local.set 3
    local.get 3
    call $summ_new_sym_var
    local.set 4
    local.get 2
    local.get 4
    i32.store offset=12
    local.get 2
    i32.load offset=12
    local.set 5
    i32.const 24
    local.set 6
    local.get 5
    local.get 6
    i32.shl
    local.set 7
    local.get 7
    local.get 6
    i32.shr_s
    local.set 8
    i32.const 16
    local.set 9
    local.get 2
    local.get 9
    i32.add
    local.set 10
    local.get 10
    global.set 0
    local.get 8
    return)
  (func $fgets (type 13) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 3
    i32.const 32
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    i32.const 32
    local.set 6
    i32.const 24
    local.set 7
    local.get 5
    local.get 7
    i32.add
    local.set 8
    local.get 8
    local.set 9
    i32.const 0
    local.set 10
    local.get 5
    local.get 0
    i32.store offset=28
    local.get 5
    local.get 1
    i32.store offset=24
    local.get 5
    local.get 2
    i32.store offset=20
    local.get 5
    local.get 10
    i32.store offset=16
    local.get 9
    local.get 6
    call $summ_is_symbolic
    local.set 11
    block  ;; label = @1
      local.get 11
      i32.eqz
      br_if 0 (;@1;)
      i32.const 32
      local.set 12
      i32.const 24
      local.set 13
      local.get 5
      local.get 13
      i32.add
      local.set 14
      local.get 14
      local.set 15
      local.get 15
      local.get 12
      call $summ_maximize
      local.set 16
      local.get 5
      local.get 16
      i32.store offset=24
    end
    block  ;; label = @1
      loop  ;; label = @2
        i32.const 0
        local.set 17
        local.get 5
        i32.load offset=24
        local.set 18
        i32.const 1
        local.set 19
        local.get 18
        local.get 19
        i32.sub
        local.set 20
        local.get 20
        local.set 21
        local.get 17
        local.set 22
        local.get 21
        local.get 22
        i32.gt_u
        local.set 23
        i32.const 1
        local.set 24
        local.get 23
        local.get 24
        i32.and
        local.set 25
        local.get 25
        i32.eqz
        br_if 1 (;@1;)
        i32.const 8
        local.set 26
        local.get 26
        call $summ_new_sym_var
        local.set 27
        local.get 5
        local.get 27
        i32.store offset=12
        local.get 5
        i32.load offset=12
        local.set 28
        local.get 5
        i32.load offset=28
        local.set 29
        local.get 5
        i32.load offset=16
        local.set 30
        i32.const 1
        local.set 31
        local.get 30
        local.get 31
        i32.add
        local.set 32
        local.get 5
        local.get 32
        i32.store offset=16
        local.get 29
        local.get 30
        i32.add
        local.set 33
        local.get 33
        local.get 28
        i32.store8
        local.get 5
        i32.load offset=24
        local.set 34
        i32.const -1
        local.set 35
        local.get 34
        local.get 35
        i32.add
        local.set 36
        local.get 5
        local.get 36
        i32.store offset=24
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 37
    local.get 5
    i32.load offset=28
    local.set 38
    local.get 5
    i32.load offset=16
    local.set 39
    local.get 38
    local.get 39
    i32.add
    local.set 40
    local.get 40
    local.get 37
    i32.store8
    local.get 5
    i32.load offset=28
    local.set 41
    i32.const 32
    local.set 42
    local.get 5
    local.get 42
    i32.add
    local.set 43
    local.get 43
    global.set 0
    local.get 41
    return)
  (func $atoi1 (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i64 i64 i64 i64 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 64
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    i32.const 1
    local.set 5
    local.get 3
    local.get 0
    i32.store offset=56
    local.get 3
    local.get 4
    i32.store offset=52
    local.get 3
    local.get 5
    i32.store offset=48
    local.get 3
    local.get 4
    i32.store offset=44
    block  ;; label = @1
      block  ;; label = @2
        loop  ;; label = @3
          i32.const 8
          local.set 6
          local.get 3
          i32.load offset=56
          local.set 7
          local.get 3
          i32.load offset=52
          local.set 8
          local.get 7
          local.get 8
          i32.add
          local.set 9
          local.get 9
          local.get 6
          call $summ_is_symbolic
          local.set 10
          block  ;; label = @4
            block  ;; label = @5
              local.get 10
              br_if 0 (;@5;)
              local.get 3
              i32.load offset=56
              local.set 11
              local.get 3
              i32.load offset=52
              local.set 12
              local.get 11
              local.get 12
              i32.add
              local.set 13
              local.get 13
              i32.load8_u
              local.set 14
              i32.const 24
              local.set 15
              local.get 14
              local.get 15
              i32.shl
              local.set 16
              local.get 16
              local.get 15
              i32.shr_s
              local.set 17
              local.get 17
              call $is_numeric
              local.set 18
              block  ;; label = @6
                block  ;; label = @7
                  local.get 18
                  i32.eqz
                  br_if 0 (;@7;)
                  local.get 3
                  i32.load offset=44
                  local.set 19
                  i32.const 10
                  local.set 20
                  local.get 19
                  local.get 20
                  i32.mul
                  local.set 21
                  local.get 3
                  i32.load offset=56
                  local.set 22
                  local.get 3
                  i32.load offset=52
                  local.set 23
                  local.get 22
                  local.get 23
                  i32.add
                  local.set 24
                  local.get 24
                  i32.load8_u
                  local.set 25
                  i32.const 24
                  local.set 26
                  local.get 25
                  local.get 26
                  i32.shl
                  local.set 27
                  local.get 27
                  local.get 26
                  i32.shr_s
                  local.set 28
                  local.get 21
                  local.get 28
                  i32.add
                  local.set 29
                  i32.const 48
                  local.set 30
                  local.get 29
                  local.get 30
                  i32.sub
                  local.set 31
                  local.get 3
                  local.get 31
                  i32.store offset=44
                  local.get 3
                  i32.load offset=52
                  local.set 32
                  i32.const 1
                  local.set 33
                  local.get 32
                  local.get 33
                  i32.add
                  local.set 34
                  local.get 3
                  local.get 34
                  i32.store offset=52
                  br 1 (;@6;)
                end
                i32.const 45
                local.set 35
                local.get 3
                i32.load offset=56
                local.set 36
                local.get 3
                i32.load offset=52
                local.set 37
                local.get 36
                local.get 37
                i32.add
                local.set 38
                local.get 38
                i32.load8_u
                local.set 39
                i32.const 24
                local.set 40
                local.get 39
                local.get 40
                i32.shl
                local.set 41
                local.get 41
                local.get 40
                i32.shr_s
                local.set 42
                local.get 42
                local.set 43
                local.get 35
                local.set 44
                local.get 43
                local.get 44
                i32.eq
                local.set 45
                i32.const 1
                local.set 46
                local.get 45
                local.get 46
                i32.and
                local.set 47
                block  ;; label = @7
                  block  ;; label = @8
                    local.get 47
                    i32.eqz
                    br_if 0 (;@8;)
                    local.get 3
                    i32.load offset=52
                    local.set 48
                    local.get 48
                    br_if 0 (;@8;)
                    i32.const -1
                    local.set 49
                    local.get 3
                    local.get 49
                    i32.store offset=48
                    local.get 3
                    i32.load offset=52
                    local.set 50
                    i32.const 1
                    local.set 51
                    local.get 50
                    local.get 51
                    i32.add
                    local.set 52
                    local.get 3
                    local.get 52
                    i32.store offset=52
                    br 1 (;@7;)
                  end
                  local.get 3
                  i32.load offset=56
                  local.set 53
                  local.get 3
                  i32.load offset=52
                  local.set 54
                  local.get 53
                  local.get 54
                  i32.add
                  local.set 55
                  local.get 55
                  i32.load8_u
                  local.set 56
                  i32.const 24
                  local.set 57
                  local.get 56
                  local.get 57
                  i32.shl
                  local.set 58
                  local.get 58
                  local.get 57
                  i32.shr_s
                  local.set 59
                  block  ;; label = @8
                    local.get 59
                    br_if 0 (;@8;)
                    br 6 (;@2;)
                  end
                  i32.const 0
                  local.set 60
                  local.get 3
                  local.get 60
                  i32.store offset=60
                  br 6 (;@1;)
                end
              end
              br 1 (;@4;)
            end
            local.get 3
            i32.load offset=44
            local.set 61
            block  ;; label = @5
              local.get 61
              br_if 0 (;@5;)
              i32.const 10
              local.set 62
              i32.const 32
              local.set 63
              local.get 63
              call $summ_new_sym_var
              local.set 64
              local.get 3
              local.get 64
              i32.store offset=40
              local.get 3
              i32.load offset=56
              local.set 65
              local.get 65
              call $strlen
              local.set 66
              local.get 3
              local.get 66
              i32.store offset=36
              local.get 3
              i32.load offset=36
              local.set 67
              local.get 67
              local.set 68
              local.get 62
              local.set 69
              local.get 68
              local.get 69
              i32.lt_s
              local.set 70
              i32.const 1
              local.set 71
              local.get 70
              local.get 71
              i32.and
              local.set 72
              block  ;; label = @6
                local.get 72
                i32.eqz
                br_if 0 (;@6;)
                i32.const 32
                local.set 73
                i32.const 28
                local.set 74
                local.get 3
                local.get 74
                i32.add
                local.set 75
                local.get 75
                local.set 76
                i32.const 40
                local.set 77
                local.get 3
                local.get 77
                i32.add
                local.set 78
                local.get 78
                local.set 79
                i32.const 32
                local.set 80
                local.get 3
                local.get 80
                i32.add
                local.set 81
                local.get 81
                local.set 82
                i32.const 10
                local.set 83
                i32.const -10
                local.set 84
                local.get 3
                i32.load offset=36
                local.set 85
                i32.const 1
                local.set 86
                local.get 85
                local.get 86
                i32.sub
                local.set 87
                local.get 84
                local.get 87
                call $pow
                local.set 88
                local.get 3
                local.get 88
                i32.store offset=32
                local.get 3
                i32.load offset=36
                local.set 89
                local.get 83
                local.get 89
                call $pow
                local.set 90
                local.get 3
                local.get 90
                i32.store offset=28
                local.get 79
                local.get 82
                local.get 73
                call $_solver_GT
                local.set 91
                local.get 3
                local.get 91
                i64.store offset=16
                local.get 79
                local.get 76
                local.get 73
                call $_solver_LT
                local.set 92
                local.get 3
                local.get 92
                i64.store offset=8
                local.get 3
                i64.load offset=16
                local.set 93
                local.get 3
                i64.load offset=8
                local.set 94
                local.get 93
                local.get 94
                call $_solver_And
                local.set 95
                local.get 3
                local.get 95
                i64.store
                local.get 3
                i64.load
                local.set 96
                local.get 96
                call $summ_assume
              end
              local.get 3
              i32.load offset=40
              local.set 97
              local.get 3
              local.get 97
              i32.store offset=60
              br 4 (;@1;)
            end
          end
          br 0 (;@3;)
        end
      end
      local.get 3
      i32.load offset=44
      local.set 98
      local.get 3
      i32.load offset=48
      local.set 99
      local.get 98
      local.get 99
      i32.mul
      local.set 100
      local.get 3
      local.get 100
      i32.store offset=60
    end
    local.get 3
    i32.load offset=60
    local.set 101
    i32.const 64
    local.set 102
    local.get 3
    local.get 102
    i32.add
    local.set 103
    local.get 103
    global.set 0
    local.get 101
    return)
  (func $atoi2 (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i64 i64 i64 i64 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 80
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    i32.const 1
    local.set 5
    local.get 3
    local.get 0
    i32.store offset=72
    local.get 3
    local.get 4
    i32.store offset=68
    local.get 3
    local.get 5
    i32.store offset=64
    local.get 3
    local.get 4
    i32.store offset=60
    local.get 3
    local.get 4
    i32.store offset=56
    local.get 3
    local.get 4
    i32.store offset=52
    block  ;; label = @1
      block  ;; label = @2
        loop  ;; label = @3
          i32.const 8
          local.set 6
          local.get 3
          i32.load offset=72
          local.set 7
          local.get 3
          i32.load offset=68
          local.set 8
          local.get 7
          local.get 8
          i32.add
          local.set 9
          local.get 9
          local.get 6
          call $summ_is_symbolic
          local.set 10
          block  ;; label = @4
            block  ;; label = @5
              local.get 10
              br_if 0 (;@5;)
              local.get 3
              i32.load offset=72
              local.set 11
              local.get 3
              i32.load offset=68
              local.set 12
              local.get 11
              local.get 12
              i32.add
              local.set 13
              local.get 13
              i32.load8_u
              local.set 14
              i32.const 24
              local.set 15
              local.get 14
              local.get 15
              i32.shl
              local.set 16
              local.get 16
              local.get 15
              i32.shr_s
              local.set 17
              local.get 17
              call $is_numeric
              local.set 18
              block  ;; label = @6
                block  ;; label = @7
                  local.get 18
                  i32.eqz
                  br_if 0 (;@7;)
                  local.get 3
                  i32.load offset=52
                  local.set 19
                  local.get 19
                  br_if 0 (;@7;)
                  local.get 3
                  i32.load offset=60
                  local.set 20
                  i32.const 10
                  local.set 21
                  local.get 20
                  local.get 21
                  i32.mul
                  local.set 22
                  local.get 3
                  i32.load offset=72
                  local.set 23
                  local.get 3
                  i32.load offset=68
                  local.set 24
                  local.get 23
                  local.get 24
                  i32.add
                  local.set 25
                  local.get 25
                  i32.load8_u
                  local.set 26
                  i32.const 24
                  local.set 27
                  local.get 26
                  local.get 27
                  i32.shl
                  local.set 28
                  local.get 28
                  local.get 27
                  i32.shr_s
                  local.set 29
                  local.get 22
                  local.get 29
                  i32.add
                  local.set 30
                  i32.const 48
                  local.set 31
                  local.get 30
                  local.get 31
                  i32.sub
                  local.set 32
                  local.get 3
                  local.get 32
                  i32.store offset=60
                  local.get 3
                  i32.load offset=68
                  local.set 33
                  i32.const 1
                  local.set 34
                  local.get 33
                  local.get 34
                  i32.add
                  local.set 35
                  local.get 3
                  local.get 35
                  i32.store offset=68
                  br 1 (;@6;)
                end
                i32.const 45
                local.set 36
                local.get 3
                i32.load offset=72
                local.set 37
                local.get 3
                i32.load offset=68
                local.set 38
                local.get 37
                local.get 38
                i32.add
                local.set 39
                local.get 39
                i32.load8_u
                local.set 40
                i32.const 24
                local.set 41
                local.get 40
                local.get 41
                i32.shl
                local.set 42
                local.get 42
                local.get 41
                i32.shr_s
                local.set 43
                local.get 43
                local.set 44
                local.get 36
                local.set 45
                local.get 44
                local.get 45
                i32.eq
                local.set 46
                i32.const 1
                local.set 47
                local.get 46
                local.get 47
                i32.and
                local.set 48
                block  ;; label = @7
                  block  ;; label = @8
                    local.get 48
                    i32.eqz
                    br_if 0 (;@8;)
                    local.get 3
                    i32.load offset=68
                    local.set 49
                    local.get 49
                    br_if 0 (;@8;)
                    i32.const -1
                    local.set 50
                    local.get 3
                    local.get 50
                    i32.store offset=64
                    local.get 3
                    i32.load offset=68
                    local.set 51
                    i32.const 1
                    local.set 52
                    local.get 51
                    local.get 52
                    i32.add
                    local.set 53
                    local.get 3
                    local.get 53
                    i32.store offset=68
                    br 1 (;@7;)
                  end
                  local.get 3
                  i32.load offset=72
                  local.set 54
                  local.get 3
                  i32.load offset=68
                  local.set 55
                  local.get 54
                  local.get 55
                  i32.add
                  local.set 56
                  local.get 56
                  i32.load8_u
                  local.set 57
                  i32.const 24
                  local.set 58
                  local.get 57
                  local.get 58
                  i32.shl
                  local.set 59
                  local.get 59
                  local.get 58
                  i32.shr_s
                  local.set 60
                  block  ;; label = @8
                    local.get 60
                    br_if 0 (;@8;)
                    br 6 (;@2;)
                  end
                  i32.const 0
                  local.set 61
                  local.get 3
                  local.get 61
                  i32.store offset=76
                  br 6 (;@1;)
                end
              end
              br 1 (;@4;)
            end
            local.get 3
            i32.load offset=72
            local.set 62
            local.get 3
            i32.load offset=68
            local.set 63
            local.get 62
            local.get 63
            i32.add
            local.set 64
            local.get 64
            call $sym_is_numeric
            local.set 65
            local.get 3
            local.get 65
            i64.store offset=40
            local.get 3
            i64.load offset=40
            local.set 66
            local.get 66
            call $_solver_is_it_possible
            local.set 67
            block  ;; label = @5
              block  ;; label = @6
                local.get 67
                i32.eqz
                br_if 0 (;@6;)
                i32.const 1
                local.set 68
                local.get 3
                i64.load offset=40
                local.set 69
                local.get 69
                call $summ_assume
                local.get 3
                local.get 68
                i32.store offset=52
                local.get 3
                i32.load offset=56
                local.set 70
                i32.const 1
                local.set 71
                local.get 70
                local.get 71
                i32.add
                local.set 72
                local.get 3
                local.get 72
                i32.store offset=56
                local.get 3
                i32.load offset=68
                local.set 73
                i32.const 1
                local.set 74
                local.get 73
                local.get 74
                i32.add
                local.set 75
                local.get 3
                local.get 75
                i32.store offset=68
                br 1 (;@5;)
              end
              br 3 (;@2;)
            end
          end
          i32.const 10
          local.set 76
          local.get 3
          i32.load offset=68
          local.set 77
          local.get 77
          local.set 78
          local.get 76
          local.set 79
          local.get 78
          local.get 79
          i32.gt_s
          local.set 80
          i32.const 1
          local.set 81
          local.get 80
          local.get 81
          i32.and
          local.set 82
          block  ;; label = @4
            local.get 82
            i32.eqz
            br_if 0 (;@4;)
            br 2 (;@2;)
          end
          br 0 (;@3;)
        end
      end
      i32.const 0
      local.set 83
      local.get 3
      i32.load offset=56
      local.set 84
      local.get 84
      local.set 85
      local.get 83
      local.set 86
      local.get 85
      local.get 86
      i32.gt_s
      local.set 87
      i32.const 1
      local.set 88
      local.get 87
      local.get 88
      i32.and
      local.set 89
      block  ;; label = @2
        local.get 89
        i32.eqz
        br_if 0 (;@2;)
        i32.const 32
        local.set 90
        local.get 90
        call $summ_new_sym_var
        local.set 91
        local.get 3
        local.get 91
        i32.store offset=36
        local.get 3
        i32.load offset=60
        local.set 92
        block  ;; label = @3
          block  ;; label = @4
            local.get 92
            br_if 0 (;@4;)
            i32.const 1
            local.set 93
            local.get 3
            i32.load offset=64
            local.set 94
            local.get 94
            local.set 95
            local.get 93
            local.set 96
            local.get 95
            local.get 96
            i32.eq
            local.set 97
            i32.const 1
            local.set 98
            local.get 97
            local.get 98
            i32.and
            local.set 99
            block  ;; label = @5
              block  ;; label = @6
                local.get 99
                i32.eqz
                br_if 0 (;@6;)
                i32.const 10
                local.set 100
                i32.const 0
                local.set 101
                local.get 3
                local.get 101
                i32.store offset=32
                local.get 3
                i32.load offset=56
                local.set 102
                local.get 100
                local.get 102
                call $pow
                local.set 103
                i32.const 1
                local.set 104
                local.get 103
                local.get 104
                i32.sub
                local.set 105
                local.get 3
                local.get 105
                i32.store offset=28
                br 1 (;@5;)
              end
              i32.const 0
              local.set 106
              i32.const 10
              local.set 107
              local.get 3
              i32.load offset=56
              local.set 108
              local.get 107
              local.get 108
              call $pow
              local.set 109
              i32.const 1
              local.set 110
              local.get 109
              local.get 110
              i32.sub
              local.set 111
              i32.const -1
              local.set 112
              local.get 111
              local.get 112
              i32.mul
              local.set 113
              local.get 3
              local.get 113
              i32.store offset=32
              local.get 3
              local.get 106
              i32.store offset=28
            end
            br 1 (;@3;)
          end
          i32.const 10
          local.set 114
          local.get 3
          i32.load offset=60
          local.set 115
          local.get 3
          i32.load offset=64
          local.set 116
          local.get 115
          local.get 116
          i32.mul
          local.set 117
          local.get 3
          i32.load offset=56
          local.set 118
          local.get 114
          local.get 118
          call $pow
          local.set 119
          local.get 117
          local.get 119
          i32.mul
          local.set 120
          local.get 3
          local.get 120
          i32.store offset=32
          local.get 3
          i32.load offset=32
          local.set 121
          local.get 3
          i32.load offset=56
          local.set 122
          local.get 114
          local.get 122
          call $pow
          local.set 123
          i32.const 1
          local.set 124
          local.get 123
          local.get 124
          i32.sub
          local.set 125
          local.get 121
          local.get 125
          i32.add
          local.set 126
          local.get 3
          local.get 126
          i32.store offset=28
        end
        i32.const 32
        local.set 127
        i32.const 28
        local.set 128
        local.get 3
        local.get 128
        i32.add
        local.set 129
        local.get 129
        local.set 130
        i32.const 36
        local.set 131
        local.get 3
        local.get 131
        i32.add
        local.set 132
        local.get 132
        local.set 133
        i32.const 32
        local.set 134
        local.get 3
        local.get 134
        i32.add
        local.set 135
        local.get 135
        local.set 136
        local.get 133
        local.get 136
        local.get 127
        call $_solver_GE
        local.set 137
        local.get 3
        local.get 137
        i64.store offset=16
        local.get 133
        local.get 130
        local.get 127
        call $_solver_LE
        local.set 138
        local.get 3
        local.get 138
        i64.store offset=8
        local.get 3
        i64.load offset=16
        local.set 139
        local.get 3
        i64.load offset=8
        local.set 140
        local.get 139
        local.get 140
        call $_solver_And
        local.set 141
        local.get 3
        local.get 141
        i64.store
        local.get 3
        i64.load
        local.set 142
        local.get 142
        call $summ_assume
        local.get 3
        i32.load offset=36
        local.set 143
        local.get 3
        local.get 143
        i32.store offset=76
        br 1 (;@1;)
      end
      local.get 3
      i32.load offset=60
      local.set 144
      local.get 3
      i32.load offset=64
      local.set 145
      local.get 144
      local.get 145
      i32.mul
      local.set 146
      local.get 3
      local.get 146
      i32.store offset=76
    end
    local.get 3
    i32.load offset=76
    local.set 147
    i32.const 80
    local.set 148
    local.get 3
    local.get 148
    i32.add
    local.set 149
    local.get 149
    global.set 0
    local.get 147
    return)
  (func $atoi (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 3
    i32.load offset=12
    local.set 4
    local.get 4
    call $atoi1
    local.set 5
    i32.const 16
    local.set 6
    local.get 3
    local.get 6
    i32.add
    local.set 7
    local.get 7
    global.set 0
    local.get 5
    return)
  (func $summ_true (type 14) (result i64)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i32 i32)
    global.get 0
    local.set 0
    i32.const 16
    local.set 1
    local.get 0
    local.get 1
    i32.sub
    local.set 2
    local.get 2
    global.set 0
    i32.const 32
    local.set 3
    i32.const 8
    local.set 4
    local.get 2
    local.get 4
    i32.add
    local.set 5
    local.get 5
    local.set 6
    i32.const 12
    local.set 7
    local.get 2
    local.get 7
    i32.add
    local.set 8
    local.get 8
    local.set 9
    i32.const 1
    local.set 10
    local.get 2
    local.get 10
    i32.store offset=12
    local.get 2
    local.get 10
    i32.store offset=8
    local.get 9
    local.get 6
    local.get 3
    call $_solver_EQ
    local.set 11
    local.get 2
    local.get 11
    i64.store
    local.get 2
    i64.load
    local.set 12
    i32.const 16
    local.set 13
    local.get 2
    local.get 13
    i32.add
    local.set 14
    local.get 14
    global.set 0
    local.get 12
    return)
  (func $_solver_must_be (type 12) (param i64) (result i32)
    (local i32 i32 i32 i32 i64 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 0
    local.set 4
    local.get 3
    local.get 0
    i64.store offset=8
    local.get 3
    i64.load offset=8
    local.set 5
    local.get 5
    call $_solver_NOT
    local.set 6
    local.get 6
    call $_solver_is_it_possible
    local.set 7
    local.get 7
    local.set 8
    local.get 4
    local.set 9
    local.get 8
    local.get 9
    i32.ne
    local.set 10
    i32.const -1
    local.set 11
    local.get 10
    local.get 11
    i32.xor
    local.set 12
    i32.const 1
    local.set 13
    local.get 12
    local.get 13
    i32.and
    local.set 14
    i32.const 16
    local.set 15
    local.get 3
    local.get 15
    i32.add
    local.set 16
    local.get 16
    global.set 0
    local.get 14
    return)
  (func $is_numeric (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    i32.const 0
    local.set 4
    i32.const 48
    local.set 5
    local.get 3
    local.get 0
    i32.store8 offset=15
    local.get 3
    i32.load8_u offset=15
    local.set 6
    i32.const 24
    local.set 7
    local.get 6
    local.get 7
    i32.shl
    local.set 8
    local.get 8
    local.get 7
    i32.shr_s
    local.set 9
    local.get 9
    local.set 10
    local.get 5
    local.set 11
    local.get 10
    local.get 11
    i32.ge_s
    local.set 12
    i32.const 1
    local.set 13
    local.get 12
    local.get 13
    i32.and
    local.set 14
    local.get 4
    local.set 15
    block  ;; label = @1
      local.get 14
      i32.eqz
      br_if 0 (;@1;)
      i32.const 57
      local.set 16
      local.get 3
      i32.load8_u offset=15
      local.set 17
      i32.const 24
      local.set 18
      local.get 17
      local.get 18
      i32.shl
      local.set 19
      local.get 19
      local.get 18
      i32.shr_s
      local.set 20
      local.get 20
      local.set 21
      local.get 16
      local.set 22
      local.get 21
      local.get 22
      i32.le_s
      local.set 23
      local.get 23
      local.set 15
    end
    local.get 15
    local.set 24
    i32.const 1
    local.set 25
    i32.const 0
    local.set 26
    i32.const 1
    local.set 27
    local.get 24
    local.get 27
    i32.and
    local.set 28
    local.get 25
    local.get 26
    local.get 28
    select
    local.set 29
    local.get 29
    return)
  (func $_solver_GE (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i32 i32 i32 i64 i64 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 5
    i32.load offset=12
    local.set 6
    local.get 5
    i32.load offset=8
    local.set 7
    local.get 5
    i32.load offset=4
    local.set 8
    local.get 6
    local.get 7
    local.get 8
    call $_solver_LT
    local.set 9
    local.get 9
    call $_solver_NOT
    local.set 10
    i32.const 16
    local.set 11
    local.get 5
    local.get 11
    i32.add
    local.set 12
    local.get 12
    global.set 0
    local.get 10
    return)
  (func $_solver_GT (type 10) (param i32 i32 i32) (result i64)
    (local i32 i32 i32 i32 i32 i32 i64 i64 i32 i32)
    global.get 0
    local.set 3
    i32.const 16
    local.set 4
    local.get 3
    local.get 4
    i32.sub
    local.set 5
    local.get 5
    global.set 0
    local.get 5
    local.get 0
    i32.store offset=12
    local.get 5
    local.get 1
    i32.store offset=8
    local.get 5
    local.get 2
    i32.store offset=4
    local.get 5
    i32.load offset=12
    local.set 6
    local.get 5
    i32.load offset=8
    local.set 7
    local.get 5
    i32.load offset=4
    local.set 8
    local.get 6
    local.get 7
    local.get 8
    call $_solver_LE
    local.set 9
    local.get 9
    call $_solver_NOT
    local.set 10
    i32.const 16
    local.set 11
    local.get 5
    local.get 11
    i32.add
    local.set 12
    local.get 12
    global.set 0
    local.get 10
    return)
  (func $sym_is_numeric (type 15) (param i32) (result i64)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i64 i64 i64 i64 i32 i32)
    global.get 0
    local.set 1
    i32.const 32
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    global.set 0
    i32.const 26
    local.set 4
    local.get 3
    local.get 4
    i32.add
    local.set 5
    local.get 5
    local.set 6
    i32.const 8
    local.set 7
    i32.const 27
    local.set 8
    local.get 3
    local.get 8
    i32.add
    local.set 9
    local.get 9
    local.set 10
    i32.const 57
    local.set 11
    i32.const 48
    local.set 12
    local.get 3
    local.get 0
    i32.store offset=28
    local.get 3
    local.get 12
    i32.store8 offset=27
    local.get 3
    local.get 11
    i32.store8 offset=26
    local.get 3
    i32.load offset=28
    local.set 13
    local.get 13
    local.get 10
    local.get 7
    call $_solver_GE
    local.set 14
    local.get 3
    local.get 14
    i64.store offset=16
    local.get 3
    i32.load offset=28
    local.set 15
    local.get 15
    local.get 6
    local.get 7
    call $_solver_LE
    local.set 16
    local.get 3
    local.get 16
    i64.store offset=8
    local.get 3
    i64.load offset=16
    local.set 17
    local.get 3
    i64.load offset=8
    local.set 18
    local.get 17
    local.get 18
    call $_solver_And
    local.set 19
    i32.const 32
    local.set 20
    local.get 3
    local.get 20
    i32.add
    local.set 21
    local.get 21
    global.set 0
    local.get 19
    return)
  (func $pow (type 2) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    global.get 0
    local.set 2
    i32.const 16
    local.set 3
    local.get 2
    local.get 3
    i32.sub
    local.set 4
    i32.const 1
    local.set 5
    local.get 4
    local.get 0
    i32.store offset=12
    local.get 4
    local.get 1
    i32.store offset=8
    local.get 4
    local.get 5
    i32.store offset=4
    block  ;; label = @1
      loop  ;; label = @2
        local.get 4
        i32.load offset=8
        local.set 6
        local.get 6
        i32.eqz
        br_if 1 (;@1;)
        local.get 4
        i32.load offset=8
        local.set 7
        i32.const 1
        local.set 8
        local.get 7
        local.get 8
        i32.and
        local.set 9
        block  ;; label = @3
          local.get 9
          i32.eqz
          br_if 0 (;@3;)
          local.get 4
          i32.load offset=12
          local.set 10
          local.get 4
          i32.load offset=4
          local.set 11
          local.get 11
          local.get 10
          i32.mul
          local.set 12
          local.get 4
          local.get 12
          i32.store offset=4
        end
        local.get 4
        i32.load offset=8
        local.set 13
        i32.const 1
        local.set 14
        local.get 13
        local.get 14
        i32.shr_u
        local.set 15
        local.get 4
        local.get 15
        i32.store offset=8
        local.get 4
        i32.load offset=12
        local.set 16
        local.get 4
        i32.load offset=12
        local.set 17
        local.get 16
        local.get 17
        i32.mul
        local.set 18
        local.get 4
        local.get 18
        i32.store offset=12
        br 0 (;@2;)
      end
    end
    local.get 4
    i32.load offset=4
    local.set 19
    local.get 19
    return)
  (func $dyn_sym_int32 (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    local.get 0
    i32.store8 offset=15
    local.get 0
    drop
    i32.const 0
    local.set 4
    local.get 4
    return)
  (func $is_symbolic (type 2) (param i32 i32) (result i32)
    local.get 0
    local.get 1
    print_stack
    print_memory
    is_symbolic)
  (func $assume (type 3) (param i32)
    (local i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 0
    drop
    return)
  (func $assert (type 3) (param i32)
    (local i32 i32 i32)
    global.get 0
    local.set 1
    i32.const 16
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 3
    local.get 3
    local.get 0
    i32.store offset=12
    local.get 0
    drop
    return)
  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66848))
  (global (;1;) i32 (i32.const 1024))
  (global (;2;) i32 (i32.const 1300))
  (global (;3;) i32 (i32.const 1024))
  (global (;4;) i32 (i32.const 66848))
  (global (;5;) i32 (i32.const 0))
  (global (;6;) i32 (i32.const 1))
  (export "memory" (memory 0))
  (export "__wasm_call_ctors" (func $__wasm_call_ctors))
  (export "__original_main" (func $__original_main))
  (export "strlen" (func $strlen))
  (export "_solver_EQ" (func $_solver_EQ))
  (export "summ_print_restriction" (func $summ_print_restriction))
  (export "main" (func $main))
  (export "__main_void" (func $__original_main))
  (export "summ_not_implemented_error" (func $summ_not_implemented_error))
  (export "summ_print_byte" (func $summ_print_byte))
  (export "summ_maximize" (func $summ_maximize))
  (export "summ_is_symbolic" (func $summ_is_symbolic))
  (export "is_symbolic" (func $is_symbolic))
  (export "summ_new_sym_var" (func $summ_new_sym_var))
  (export "summ_assume" (func $summ_assume))
  (export "assume" (func $assume))
  (export "_solver_Concat" (func $_solver_Concat))
  (export "_solver_Extract" (func $_solver_Extract))
  (export "_solver_ZeroExt" (func $_solver_ZeroExt))
  (export "_solver_SignExt" (func $_solver_SignExt))
  (export "_solver_NOT" (func $_solver_NOT))
  (export "_solver_Or" (func $_solver_Or))
  (export "_solver_And" (func $_solver_And))
  (export "_solver_NEQ" (func $_solver_NEQ))
  (export "_solver_LT" (func $_solver_LT))
  (export "_solver_LE" (func $_solver_LE))
  (export "_solver_SLT" (func $_solver_SLT))
  (export "_solver_SLE" (func $_solver_SLE))
  (export "_solver_IF" (func $_solver_IF))
  (export "_solver_is_it_possible" (func $_solver_is_it_possible))
  (export "strlen1" (func $strlen1))
  (export "strlen2" (func $strlen2))
  (export "strncmp1" (func $strncmp1))
  (export "strncmp2" (func $strncmp2))
  (export "summ_true" (func $summ_true))
  (export "strncmp" (func $strncmp))
  (export "strcmp1" (func $strcmp1))
  (export "strcmp2" (func $strcmp2))
  (export "strcmp" (func $strcmp))
  (export "strcpy1" (func $strcpy1))
  (export "strcpy2" (func $strcpy2))
  (export "strcpy" (func $strcpy))
  (export "strncpy1" (func $strncpy1))
  (export "strncpy2" (func $strncpy2))
  (export "strncpy" (func $strncpy))
  (export "strcat1" (func $strcat1))
  (export "strcat2" (func $strcat2))
  (export "strcat" (func $strcat))
  (export "puts1" (func $puts1))
  (export "puts2" (func $puts2))
  (export "puts" (func $puts))
  (export "putchar" (func $putchar))
  (export "getchar" (func $getchar))
  (export "fgets" (func $fgets))
  (export "atoi1" (func $atoi1))
  (export "is_numeric" (func $is_numeric))
  (export "pow" (func $pow))
  (export "_solver_GT" (func $_solver_GT))
  (export "atoi2" (func $atoi2))
  (export "sym_is_numeric" (func $sym_is_numeric))
  (export "_solver_GE" (func $_solver_GE))
  (export "atoi" (func $atoi))
  (export "_solver_must_be" (func $_solver_must_be))
  (export "dyn_sym_int32" (func $dyn_sym_int32))
  (export "assert" (func $assert))
  (export "__dso_handle" (global 1))
  (export "__data_end" (global 2))
  (export "__global_base" (global 3))
  (export "__heap_base" (global 4))
  (export "__memory_base" (global 5))
  (export "__table_base" (global 6))
  (data (;0;) (i32.const 1024) "test\00summ_print_byte\00summ_maximize\00summ_new_sym_var\00_solver_Concat\00_solver_Extract\00_solver_ZeroExt\00_solver_SignExt\00summ_print_restriction\00_solver_NOT\00_solver_Or\00_solver_And\00_solver_EQ\00_solver_NEQ\00_solver_LT\00_solver_LE\00_solver_SLT\00_solver_SLE\00_solver_IF\00_solver_is_it_possible\00"))
