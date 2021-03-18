;; Must pass
;; Tests i64 arithmetic
(module 
    (memory $0 1)

    (func $main
        (sym_int64 "x")
        (sym_int64 "y")
        (i64.gt_s)
        (if                 ;; if x > y
            (then
                (get_sym_int64 "x")
                (get_sym_int64 "y")
                (i64.add)             ;; x = x+y
                (duplicate)           ;; x here again        
                (get_sym_int64 "y") 
                (i64.sub)             ;; y = x-y
                (i64.sub)             ;; x = x-y
                (get_sym_int64 "x")   ;; este x(antigo) equivale ao novo y
                (i64.le_s)            ;; x <= y
                (sym_assert)          ;; assert x <= y
            )

        )
    )
    (export "main" (func $main))
)
(invoke "main")