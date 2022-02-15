;; Must pass
;; Tests f32 sqrt
(module
    (func $main (local f32)
        (i32.const 1024)
        (f32.symbolic)      ;; retorna uma sym var com um valor random e a label `a`
        (local.tee 0)
        (f32.sqrt)          ;; sqrt(*a*)
        (f32.const 8)
        (f32.eq)
        (sym_assume)        ;; assume sqrt(*a*) == 8

        (local.get 0)
        (f32.const 64)
        (f32.eq)
        (local.get 0)
        (f32.const 16)
        (f32.eq)
        (i32.__logor)
        (sym_assume)        ;; assume *a* == 64 || *a* == 16

        (local.get 0)
        (f32.const 64)
        (f32.eq)
        (sym_assert)        ;; assert *a* == 64
    )
    (export "main" (func $main))
    (memory $0 1)
    (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
