(letrec ((fac (lambda (x)
  (letrec ((st 0) (acc 1)) (begin
    (callcc (lambda (k) (set! st k)))
    (if (eqv? x 0) acc (st (begin (set! acc ( * acc x)) (set! x (- x 1)))))))))) (fac 6))
