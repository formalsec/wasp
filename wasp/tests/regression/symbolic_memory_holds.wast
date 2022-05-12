;; Loads symbolic memory in various iterations
(module
  (type $0 (func))
  (func $test_symbolic_memory (type $0)
        (i32.const 1024)
        (i32.load8_u)
        (i32.const 120)
        (i32.eq)
        (sym_assert))

  (func $main (type $0)
        (call $test_symbolic_memory)
        (i32.const 1024)
        (i32.symbolic)      ;; x
        (i32.const 0)
        (i32.eq)
        (if
          (then
            (call $test_symbolic_memory)
            (i32.const 1026)
            (i32.symbolic)      ;; y
            (i32.const 0)
            (i32.eq)
            (if
              (then
                (call $test_symbolic_memory)
                (i32.const 1028)
                (i32.symbolic)      ;; z
                (i32.const 0)
                (i32.eq)
                (if
                  (then
                    (call $test_symbolic_memory))))))))
  (memory $0 1)
  (global $0 (mut i32) (i32.const 66592))
  (export "main" (func $main))
  (data $0 (i32.const 1024) "x\00y\00z\00"))
(invoke "main")
