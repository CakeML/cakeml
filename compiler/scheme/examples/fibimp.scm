(letrec
    ((fib (lambda (n)
              (letrec* ((a 0) (b 1) (c 0) (j (call/cc (lambda (cc) cc))))
                  (if (eqv? n 0) a
                      (begin
                       (set! c a)
                       (set! a (+ a b))
                       (set! b c)
                       (set! n (- n 1))
                       (j j)))))))
    (eqv? (fib 10) 55))
