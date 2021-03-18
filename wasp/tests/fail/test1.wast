;; Must fail
;; Tests if stored value in memory is still equal to x and different than z
(module 
    (memory $0 1)

    (func $main (result i32)
        (i32.const 1)                   ;; address number
        (sym_int32 "x")                 ;; value
        (i32.store offset=0)            ;; store in offset
        (i32.const 0)
        (get_sym_int32 "x")
        (i32.eq)
        (sym_assume)                    ;; assume( x = 0 )
        (sym_int32 "y")
        (sym_int32 "z")
        (i32.add)                       ;; y + z
        (i32.const 0)
        (i32.gt_s)                      ;; (y + z) < 0
        (if (result i32)                ;; if ((y + z) < 0)
            (then
                (get_sym_int32 "x")
            )
            (else
                (get_sym_int32 "z")
            )
        )
        (i32.const 1)
        (i32.load offset=0) ;; loads x
        (print_stack)
        (print_memory)
        (i32.eq)            ;; checks if the loaded value is equal to the one on top of stack (either x or z)
        (sym_assert)


        (i32.const 0) ;;return
    )
    (export "main" (func $main))
)
(invoke "main")
