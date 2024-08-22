;; Must fail
;; Tests f64 arithmetic
(module
    (memory $0 1)

    (func $main (result i32)
        (i32.const 1024)                ;; x
        (f64.symbolic)
        (i32.const 1026)                ;; y
        (f64.symbolic)
        (get_sym_float64 "y")
        (f64.mul)
        (f64.eq)
        (get_sym_float64 "x")
        (f64.const 0)
        (f64.ne)
        (sym_assume)                ;; assume( x != 0 )
        (if (result i32)            ;; if( x == (y * y) )
            (then
                (get_sym_float64 "x")
                (get_sym_float64 "y")
                (get_sym_float64 "y")
                (f64.div)
                (f64.eq)
                (print_stack)
                (sym_assert)        ;; assert( x == (y / y) )
                (i32.const 0)
            )
            (else
                (i32.const 0)
            )

        )
    )
    (export "main" (func $main))
    (data $0 (i32.const 1024) "x\00y\00z\00")
)
(invoke "main")
