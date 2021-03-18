;; Must fail
;; Tests f64 arithmetic
(module 
    (memory $0 1)

    (func $main
        (sym_float64 "a")
        (sym_float64 "b")
        (drop)
        (f64.const 0)
        (f64.ne)
        (if (result f64)                ;; if a != 0
            (then
                (get_sym_float64 "b")
                (f64.const 0)
                (f64.eq)
                (if	(result f64)		;; if b == 0
                	(then
                		(get_sym_float64 "a")
                		(get_sym_float64 "b")
                		(f64.add)
                		(f64.const 2)
                		(f64.mul) 			;;x = (a+b) * 2
                		(f64.const 4)		;;y = 4
                		(f64.sub)			;;x-y 
                	)
                	(else
                		(f64.const 3)
                	)
                )
            )
            (else
            	(f64.const 1)
            )

        )
        (f64.const 0)
        (f64.ne)		;; x-y != 0
        (sym_assert)
    )
    (export "main" (func $main))
)
(invoke "main")
