;; Must fail
;; Tests f64 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)                ;; a
        (f64.symbolic)
        (f64.const 0)
        (f64.gt)
        (if (result f64)            ;; if a > 0
            (then
                (f64.const -2)      ;; x = -2
            )
            (else
                (f64.const 0)       ;; x = 0
            )
        )

        (i32.const 1026)                ;; b
        (f64.symbolic)
        (f64.const 5)
        (f64.lt)
        (if (result f64)                        ;; if b < 5
            (then
                (get_sym_float64 "a")
                (f64.const 0)
                (f64.lt)
                (if (result f64)                ;; if a < 0
                    (then
                        (i32.const 1028)                ;; c
                        (f64.symbolic)
                        (f64.const 0)
                        (f64.gt)
                        (if (result f64)            ;; if a < 0 && c > 0
                            (then
                                (f64.const 1) ;; y = 1
                            )
                            (else
                                (f64.const 0)   ;; y = 0
                            )
                        )
                    )
                    (else
                        (f64.const 0)   ;; y = 0
                    )
                )
                (f64.const 2)       ;; z = 2
                (f64.add)           ;; y + z
            )
            (else
                (f64.const 0)       ;; y + z = 0
            )
        )
        (f64.add)   ;; x + y + z
        (f64.const 3)
        (f64.ne)
        (sym_assert)    ;; assert x+y+z != 3

    )

    (export "main" (func $main))
    (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
