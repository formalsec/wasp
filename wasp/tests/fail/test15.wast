;; Must fail
;; Tests f32 arithmetic
(module 
    (memory $0 1)

    (func $main
        (sym_float32 "a")
        (sym_float32 "b")
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
)
(invoke "main")
