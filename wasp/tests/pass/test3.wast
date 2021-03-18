;; Must pass
;; Tests i32 arithmetic
(module 
    (memory $0 1)

    (func $main
        (sym_int32 "x")
        (sym_int32 "y")
        (i32.gt_s)
        (if                 ;; if x > y
            (then
                (get_sym_int32 "x")
                (get_sym_int32 "y")
                (i32.add)             ;; x = x+y
                (duplicate)           ;; x here again        
                (get_sym_int32 "y") 
                (i32.sub)             ;; y = x-y
                (i32.sub)             ;; x = x-y
                (get_sym_int32 "x")   ;; este x(antigo) equivale ao novo y
                (i32.le_s)            ;; x <= y
                (sym_assert)          ;; assert x <= y
            )

        )
    )
    (export "main" (func $main))
)
(invoke "main")