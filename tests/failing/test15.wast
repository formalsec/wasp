;; Must fail
;; Tests f32 arithmetic
(module
    (memory $0 1)

    (func $main
        (i32.const 1024)                ;; a
        (f32.symbolic)
        (i32.const 1026)                ;; b
        (f32.symbolic)
        (drop)
        (f32.const 0)
        (f32.ne)
        (if (result f32)                ;; if a != 0
            (then
                (get_sym_float32 "b")
                (f32.const 0)
                (f32.eq)
                (if	(result f32)		;; if b == 0
                	(then
                		(get_sym_float32 "a")
                		(get_sym_float32 "b")
                		(f32.add)
                		(f32.const 2)
                		(f32.mul) 			;;x = (a+b) * 2
                		(f32.const 4)		;;y = 4
                		(f32.sub)			;;x-y
                	)
                	(else
                		(f32.const 3)
                	)
                )
            )
            (else
            	(f32.const 1)
            )

        )
        (f32.const 0)
        (f32.ne)		;; x-y != 0
        (sym_assert)
    )
    (export "main" (func $main))
    (data $0 (i32.const 1024) "a\00b\00c\00")
)
(invoke "main")
