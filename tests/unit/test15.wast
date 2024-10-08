;; Must fail
;; Tests i32 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)                ;; a
        (i32.symbolic)
        (i32.const 1026)                ;; a
        (i32.symbolic)
        (drop)
        (i32.const 0)
        (i32.ne)
        (if (result i32)                ;; if a != 0
            (then
                (get_sym_int32 "b")
                (i32.const 0)
                (i32.eq)
                (if	(result i32)		;; if b == 0
                	(then
                		(get_sym_int32 "a")
                		(get_sym_int32 "b")
                		(i32.add)
                		(i32.const 2)
                		(i32.mul) 			;;x = (a+b) * 2
                		(i32.const 4)		;;y = 4
                		(i32.sub)			;;x-y
                	)
                	(else
                		(i32.const 3)
                	)
                )
            )
            (else
            	(i32.const 1)
            )

        )
        (i32.const 0)
        (i32.ne)		;; x-y != 0
        (sym_assert)
    )
    (export "main" (func $main))
    (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
