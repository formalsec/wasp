;; Loads symbolic memory in various iterations 
(module
  (type $0 (func))
  (type $1 (func (param i32)))

  (func $test_globals (type $1) (param i32)
        (global.get 0)
        (print_stack)
        (i32.const 1024)
        (i32.sub)
        (global.set 0)
        (global.get 0)
        (local.get 0)
        (i32.eq)
        (sym_assert))

  (func $main (type $0)
        (i32.const 65568)
        (call $test_globals)
        (sym_int32 "if@16")
        (i32.const 0)
        (i32.eq)
        (if 
          (then
            (i32.const 64544)
            (call $test_globals)
            (sym_int32 "if@22")
            (i32.const 0)
            (i32.eq)
            (if
              (then
                (i32.const 63520)
                (call $test_globals)
                (sym_int32 "if@28")
                (i32.const 0)
                (i32.eq)
                (if
                  (then
                    (i32.const 62496)
                    (call $test_globals))))))))
  (memory $0 1)
  (global $0 (mut i32) (i32.const 66592))
  (global $1 i32 (i32.const 0))
  (global $2 i32 (i32.const 1))
  (export "main" (func $main))
  (data $0 (i32.const 1024) "x\00y\00"))
(invoke "main")
