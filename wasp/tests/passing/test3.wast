;; Must pass
;; Tests i32 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)    ;; x
        (i32.symbolic)
        (i32.const 1026)    ;; y
        (i32.symbolic)
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
    (data $0 (i32.const 1024) "x\00y\00z\00")
)
(invoke "main")
