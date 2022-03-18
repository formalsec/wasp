;; Must fail
;; Tests i32 underflow
(module
    (func $main (local i32) (local i32)
        (i32.const 1026)
        (i32.symbolic)      ;; retorna uma sym var com um valor random e a label `b`
        (i32.const 1024)
        (i32.symbolic)      ;; retorna uma sym var com um valor random e a label `a`
        (local.tee 0)       ;; guardar a
        (i32.const 0)
        (i32.lt_s)
        (sym_assume)        ;; assume a < 0

        (local.tee 1)       ;; guardar b
        (local.get 0)       ;; buscar a
        (i32.const 1)
        (i32.sub)           ;; a - 1
        (i32.eq)            ;; b == a - 1
        (sym_assume)        ;; assume b == a - 1

        (local.get 1)       ;; buscar b
        (i32.const 0)
        (i32.lt_s)
        (sym_assert)        ;; assert b < 0
    )
    (memory $0 1)
    (export "main" (func $main))
    (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
