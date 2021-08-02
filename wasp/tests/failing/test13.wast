;; Must fail
;; Tests f64 arithmetic
(module 
    (memory $0 1)

    (func $main
        (sym_float64 "a")
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

        (sym_float64 "b")
        (f64.const 5)
        (f64.lt)
        (if (result f64)                        ;; if b < 5
            (then
                (get_sym_float64 "a")
                (f64.const 0)
                (f64.lt)
                (if (result f64)                ;; if a < 0
                    (then
                        (sym_float64 "c")
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
)
(invoke "main")




