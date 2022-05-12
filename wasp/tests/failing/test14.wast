;; Must fail
;; Tests i64 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)                ;; a
        (i64.symbolic)
        (i32.const 1026)                ;; b
        (i64.symbolic)
        (drop)
        (i64.const 0)
        (i64.ne)
        (if (result i64)                ;; if a != 0
            (then
                (get_sym_int64 "b")
                (i64.const 0)
                (i64.eq)
                (if	(result i64)		;; if b == 0
                	(then
                		(get_sym_int64 "a")
                		(get_sym_int64 "b")
                		(i64.add)
                		(i64.const 2)
                		(i64.mul) 			;;x = (a+b) * 2
                		(i64.const 4)		;;y = 4
                		(i64.sub)			;;x-y
                	)
                	(else
                		(i64.const 3)
                	)
                )
            )
            (else
            	(i64.const 1)
            )

        )
        (i64.const 0)
        (i64.ne)		;; x-y != 0
        (sym_assert)
    )
    (export "main" (func $main))
    (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
