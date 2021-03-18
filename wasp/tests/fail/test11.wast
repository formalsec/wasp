;; Must fail
;; Tests f32 arithmetic
(module 
    (memory $0 1)

    (func $main
        (sym_float32 "a")
        (f32.const 0)
        (f32.gt)
        (if (result f32)            ;; if a > 0
            (then
                (f32.const -2)      ;; x = -2
            )
            (else   
                (f32.const 0)       ;; x = 0
            )
        )

        (sym_float32 "b")
        (f32.const 5)
        (f32.lt)
        (if (result f32)                        ;; if b < 5
            (then
                (get_sym_float32 "a")
                (f32.const 0)
                (f32.lt)
                (if (result f32)                ;; if a < 0
                    (then
                        (sym_float32 "c")
                        (f32.const 0)
                        (f32.gt)
                        (if (result f32)            ;; if a < 0 && c > 0
                            (then
                                (f32.const 1) ;; y = 1
                            )
                            (else
                                (f32.const 0)   ;; y = 0
                            )
                        )
                    )
                    (else
                        (f32.const 0)   ;; y = 0
                    )
                )
                (f32.const 2)       ;; z = 2
                (f32.add)           ;; y + z
            )
            (else
                (f32.const 0)       ;; y + z = 0
            )
        )
        (f32.add)   ;; x + y + z
        (f32.const 3)
        (f32.ne)    
        (sym_assert)    ;; assert x+y+z != 3

    )
        
    (export "main" (func $main))
)
(invoke "main")




