;; Must fail
;; Tests f32 arithmetic
(module 
    (memory $0 1)

    (func $main (result i32)
        (sym_float32 "x")
        (sym_float32 "y")
        (get_sym_float32 "y")
        (f32.mul)
        (f32.eq)
        (get_sym_float32 "x")
        (f32.const 0)
        (f32.ne)
        (sym_assume)                ;; assume( x != 0 )
        (if (result i32)            ;; if( x == (y * y) )
            (then
                (get_sym_float32 "x")
                (get_sym_float32 "y")
                (get_sym_float32 "y")
                (f32.div)
                (f32.eq)
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