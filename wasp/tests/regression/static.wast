;; Must pass
(module
  (func $main (local i32)
    (i32.const 1024)
    (i32.symbolic)      ;; retorna uma sym var com um valor random e a label `a`
    (if
      (then
        (i32.const 1)
        (sym_assert)
      )
      (else
        (i32.const 1024)
        (i32.symbolic)      ;; retorna uma sym var com um valor random e a label `a`
        (sym_assert)
        )
    )
  )
  (export "main" (func $main))
  (memory $0 1)
  (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
