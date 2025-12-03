(letrec
    ((fib (lambda (n)
              (if (eqv? n 0) n
                   (if (eqv? n 1) n
                       (+ (fib (- n 1))
                          (fib (- n 2))))))))
    (eqv? (fib 10) 55))
