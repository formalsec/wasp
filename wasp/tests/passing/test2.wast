;; Must pass
;; Tests assume/assert operations
(module
    (memory $0 1)

    (func $main (local i32) (local i32) (local i32)
        (i32.const 1024)      ;; x
        (i32.symbolic)
        (local.tee 0)
        (i32.const 1026)      ;; y
        (i32.symbolic)
        (local.tee 1)
        (i32.mul)
        (i32.const 1028)      ;; z
        (i32.symbolic)
        (local.tee 2)
        (i32.ne)
        (sym_assume)          ;; assume ( x*y != z )

        (local.get 0)         ;; x
        (local.get 1)         ;; y
        (i32.mul)
        (local.get 2)         ;; z
        (i32.ne)
        (sym_assert)        ;; assert ( x*y != z ) TO PROVE THE ASSUMPTION WAS MADE
    )
    (export "main" (func $main))
    (data $0 (i32.const 1024) "x\00y\00z\00")
)
(invoke "main")
