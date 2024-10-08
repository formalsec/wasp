;; Must fail
;; Tests i64 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)                ;; a
        (i64.symbolic)
        (i64.const 0)
        (i64.gt_s)
        (if (result i64)            ;; if a > 0
            (then
                (i64.const -2)      ;; x = -2
            )
            (else
                (i64.const 0)       ;; x = 0
            )
        )

        (i32.const 1026)                ;; b
        (i64.symbolic)
        (i64.const 5)
        (i64.lt_s)
        (if (result i64)                        ;; if b < 5
            (then
                (get_sym_int64 "a")
                (i64.const 0)
                (i64.lt_s)
                (if (result i64)                ;; if a < 0
                    (then
                        (i32.const 1028)                ;; c
                        (i64.symbolic)
                        (i64.const 0)
                        (i64.gt_s)
                        (if (result i64)            ;; if a < 0 && c > 0
                            (then
                                (i64.const 1) ;; y = 1
                            )
                            (else
                                (i64.const 0)   ;; y = 0
                            )
                        )
                    )
                    (else
                        (i64.const 0)   ;; y = 0
                    )
                )
                (i64.const 2)       ;; z = 2
                (i64.add)           ;; y + z
            )
            (else
                (i64.const 0)       ;; y + z = 0
            )
        )
        (i64.add)   ;; x + y + z
        (i64.const 3)
        (i64.ne)
        (sym_assert)    ;; assert x+y+z != 3

    )

    (export "main" (func $main))
    (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
