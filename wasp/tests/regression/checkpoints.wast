(module
  (type $0 (func (param i32) (result i32)))
  (type $1 (func))
  (type $2 (func (param i32 i32 i32)))

  (func $is_power_of_two (type $0)
        (local.get 0) ;; stack: x
        (local.get 0) ;; stack: x,x
        (i32.const 1) ;; stack: 1,x,x
        (i32.sub)     ;; stack: (x - 1),x
        (i32.and)     ;; stack: (x & (x - 1))
        (i32.eqz))    ;; stack: (x & (x - 1)) = 0
  (func $test_two_concrete_one_symbolic_locals_restart (type $2)
        (local.get 0)
        (call $is_power_of_two)
        (if 
          (then
            (local.get 1)
            (call $is_power_of_two)
            (if
              (then
                (local.get 2)
                (print_stack)
                (call $is_power_of_two)
                (if
                  (then
                    (local.get 2)
                    (i32.const 0)
                    (i32.ge_u)
                    print_stack
                    (sym_assert)
                    (local.get 2)
                    (i32.const 2)
                    (i32.mul)
                    (i32.const 2)
                    (i32.ne)
                    (if
                      (then
                        (i32.const 1)
                        (print_stack)
                        (sym_assert))
                      (else
                        (i32.const 2)
                        (print_stack)
                        (sym_assert))))
                  (else
                    (i32.const 5)
                    (print_stack)
                    (local.get 2)
                    (i32.ge_s)
                    (if 
                      (then
                        (i32.const 4)
                        (print_stack)
                        (sym_assert))
                      (else
                        (i32.const 5)
                        (print_stack)
                        (sym_assert)))

                  )))))))
  (func $main (type $1)
        (i32.const 8)
        (i32.const 16)
        (i32.const 1024)
        (i32.symbolic)
        (call $test_two_concrete_one_symbolic_locals_restart))
  (memory $0 1)
  (global $0 (mut i32) (i32.const 66592))
  (export "main" (func $main))
  (data $0 (i32.const 1024) "x\00y\00"))
(invoke "main")
