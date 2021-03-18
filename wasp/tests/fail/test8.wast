;; Must fail
;; Tests i64 arithmetic
(module 
    (memory $0 1)

    (func $main (result i32)
        (sym_int64 "x")
        (sym_int64 "y")
        (get_sym_int64 "y")
        (i64.mul)
        (i64.eq)
        (get_sym_int64 "x")
        (i64.const 0)
        (i64.ne)
        (sym_assume)                ;; assume( x != 0 )
        (if (result i32)            ;; if( x == (y * y) )
            (then
                (get_sym_int64 "x")
                (get_sym_int64 "y")
                (get_sym_int64 "y")
                (i64.div_s)
                (i64.eq)
                (sym_assert)        ;; assert( x == (y / y) )
                (i32.const 0)
            )
            (else
                (i32.const 0)
            )

        )
    )
    (export "main" (func $main))
)
(invoke "main")