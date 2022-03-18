;; Must fail
;; Tests i32 underflow
(module
    (type $0 (func))
    (func $main (type $0) (local i32)
        (i32.const 1024)
        (i32.symbolic)
        (local.tee 0)
        (i32.const 0)
        (i32.lt_s)
        (if
            (then
                (local.get 0)
                (i32.const 1)
                (i32.sub)
                (i32.const 0)
                (i32.lt_s)
                (sym_assert)
            )
        )
    )
    (memory $0 1)
    (export "main" (func $main))
    (data $0 (i32.const 1024) "a\00b\00c\00"))
(invoke "main")
