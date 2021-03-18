;; Must fail
;; Tests i32 logical operations
(module 
    (memory $0 1)

    (func $main
        (sym_int32 "x")
        (sym_int32 "y")
        (i32.lt_s)
        (if                 ;; if (x < y)
            (then
                (get_sym_int32 "x")
                (get_sym_int32 "y")
                (i32.ge_s)
                (sym_assert)        ;; assert (x >= y)
            )
            (else
                (get_sym_int32 "x")
                (get_sym_int32 "y")
                (i32.lt_s)
                (sym_assert)        ;; assert (x < y)
            )
        )

    )
    (export "main" (func $main))
)
(invoke "main")
