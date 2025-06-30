(letrec
    ((nondet
      (lambda (fun)
          (call/cc
           (lambda (cc)
               (letrec ((k cc))
                   (fun
                    (lambda (f n m)
                         (letrec ((i n)
                                  (last k))
                             (begin
                              (call/cc
                               (lambda (cc) (set! k (lambda (v) (begin (set! i (+ i 1)) (cc v))))))
                              (if (eqv? i m)
                                  (begin (set! k last) (k (- 1)))
                                  (f i)))))
                    (lambda () (k (- 1)))))))))

     (triangle
      (lambda (n)
          (if (eqv? n 0) n
              (+ n (triangle (- n 1))))))
     (fib
      (lambda (n)
          (if (eqv? n 0) n
              (if (eqv? n 1) n
                  (+ (fib (- n 1))
                     (fib (- n 2))))))))

    ;(display
     (nondet
      (lambda (choose fail)
          (letrec ((x (choose triangle 3 10))
                   (y (choose fib 3 10)))
              (if (eqv? x y) x (fail))))));)
