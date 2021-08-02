;; Must pass
;; Tests assume/assert operations
(module 
    (memory $0 1)

    (func $main
        (sym_int32 "x")
        (sym_int32 "y")
        (i32.mul)
        (sym_int32 "z")
        (i32.ne)
        (sym_assume)          ;; assume ( x*y != z )

        (sym_int32 "x")
        (sym_int32 "y")
        (i32.mul)
        (sym_int32 "z")
        (i32.ne)
        (sym_assert)        ;; assert ( x*y != z ) TO PROVE THE ASSUMPTION WAS MADE
    )
    (export "main" (func $main))
)
(invoke "main")