;; Must fail
;; Tests i64 arithmetic
(module
    (memory $0 1)

    (func $constraints (param i64) (result i64)
        (local.get 0)
        (i64.const 0)
        (i64.gt_s)
        (local.get 0)
        (i64.const 9_999)
        (i64.le_s)
        (i32.and)
        (sym_assume)
        (local.get 0))

    (func $main (result i32)
        (i32.const 1024)                ;; x
        (i64.symbolic)
        (call $constraints)
        (i32.const 1026)                ;; x
        (i64.symbolic)
        (call $constraints)
        (get_sym_int64 "y")
        (i64.mul)
        (i64.eq)
        (get_sym_int64 "x")
        (i64.const 0)
        (i64.ne)
        (sym_assume)                ;; assume( x != 0 )
        (if (result i32)            ;; if( x == (y * y) )
            (then
                (get_sym_int64 "x")
                (get_sym_int64 "y")
                (get_sym_int64 "y")
                (i64.div_s)
                (i64.eq)
                (sym_assert)        ;; assert( x == (y / y) )
                (i32.const 0)
            )
            (else
                (i32.const 0)
            )

        )
    )
    (export "main" (func $main))
    (data $0 (i32.const 1024) "x\00y\00z\00")
)
(invoke "main")
