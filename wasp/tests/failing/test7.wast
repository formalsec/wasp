;; Must fail
;; Tests i32 logical operations
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)    ;; x
        (i32.symbolic)
        (i32.const 1026)    ;; y
        (i32.symbolic)
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
    (data $0 (i32.const 1024) "x\00y\00z\00")
)
(invoke "main")
