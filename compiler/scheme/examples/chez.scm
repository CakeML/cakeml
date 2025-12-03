(letrec ((f (lambda ()
                 (letrec ((a 4) (j (call/cc (lambda (cc) cc))))
                     (if (eqv? j 0)
                         a
                         (begin
                          (set! a 9)
                          (j 0)))))))
      (eqv? 4 (if #t (f) (f))))
      ;(if #t (f) 0))
