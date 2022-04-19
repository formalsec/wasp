;; Must pass
;; Tests i64 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)    ;; x
        (i64.symbolic)
        (i32.const 1026)    ;; y
        (i64.symbolic)
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
    (data $0 (i32.const 1024) "x\00y\00z\00")
)
(invoke "main")
