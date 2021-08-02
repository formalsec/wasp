;; Must pass
;; Tests f32 arithmetic
(module 
    (memory $0 1)

    (func $main
        (local f32)
        (sym_float32 "x")
        (sym_float32 "y")
        (f32.gt)
        (if                 ;; if x > y
            (then
                (i32.const 1)
                (get_sym_float32 "x")
                (get_sym_float32 "y")
                (f32.add)             ;; x = x+y
                (duplicate)           ;; x here again        
                (get_sym_float32 "y") 
                (f32.sub)             ;; y = x-y
                (f32.sub)             ;; x = x-y
                (f32.store offset=0)
                (i32.const 1)
                (f32.load offset=0)
                (get_sym_float32 "x")   ;; este x(antigo) equivale ao novo y
                (f32.le)            ;; x <= y
                (sym_assert)          ;; assert x <= y
            )

        )
    )
    (export "main" (func $main))
)
(invoke "main")
