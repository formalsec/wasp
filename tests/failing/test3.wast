;; Must fail
;; Tests i32 arithmetic
(module
    (memory $0 1)

    (func $main (result i32)
        (i32.const 1024)                ;; x
        (i32.symbolic)
        (i32.const 1026)                ;; y
        (i32.symbolic)
        (get_sym_int32 "y")
        (i32.mul)
        (i32.eq)
        (get_sym_int32 "x")
        (i32.const 0)
        (i32.ne)
        (sym_assume)                ;; assume( x != 0 )
        (if (result i32)            ;; if( x == (y * y) )
            (then
                (get_sym_int32 "x")
                (get_sym_int32 "y")
                (get_sym_int32 "y")
                (i32.div_s)
                (i32.eq)
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
