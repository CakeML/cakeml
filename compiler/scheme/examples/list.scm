(letrec
    ((length (lambda (x)
                 (if (null? x) 0
                     (+ 1 (length (cdr x)))))))
    ((lambda x (length x)) 1 2 3 5 5 5 5))
