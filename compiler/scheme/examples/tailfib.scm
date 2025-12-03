(letrec
    ((fib (lambda (n a b)
              (if (eqv? n 0) a
                  (fib (- n 1) (+ a b) a)))))
    (eqv? (fib 10 0 1) 55))
