;; Must pass
;; Tests f64 arithmetic
(module 
    (memory $0 1)

    (func $main
        (sym_float64 "x")
        (sym_float64 "y")
        (f64.gt)
        (if                 ;; if x > y
            (then
                (get_sym_float64 "x")
                (get_sym_float64 "y")
                (f64.add)             ;; x = x+y
                (duplicate)           ;; x here again        
                (get_sym_float64 "y") 
                (f64.sub)             ;; y = x-y
                (f64.sub)             ;; x = x-y
                (get_sym_float64 "x")   ;; este x(antigo) equivale ao novo y
                (f64.le)            ;; x <= y
                (sym_assert)          ;; assert x <= y
            )

        )
    )
    (export "main" (func $main))
)
(invoke "main")