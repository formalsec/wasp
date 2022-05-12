;; Must pass
;; Tests f32 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)    ;; x
        (f32.symbolic)
        (i32.const 1026)    ;; y
        (f32.symbolic)
        (f32.gt)
        (if                 ;; if x > y
            (then
                (get_sym_float32 "x")
                (get_sym_float32 "y")
                (f32.add)             ;; x = x+y
                (duplicate)           ;; x here again
                (get_sym_float32 "y")
                (f32.sub)             ;; y = x-y
                (f32.sub)             ;; x = x-y
                (get_sym_float32 "x")   ;; este x(antigo) equivale ao novo y
                (f32.le)            ;; x <= y
                (sym_assert)          ;; assert x <= y
            )

        )
    )
    (export "main" (func $main))
    (data $0 (i32.const 1024) "x\00y\00z\00")
)
(invoke "main")
