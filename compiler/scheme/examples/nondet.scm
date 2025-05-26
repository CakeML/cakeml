(letrec
    ((nondet
      (lambda (fun)
          (call/cc
           (lambda (cc)
               (letrec
                   ((fail (lambda () (cc (- 1))))
                    (choose
                     (lambda (f n m)
                         (letrec
                             ((i n)
                              (last fail))
                             (begin
                              (call/cc
                               (lambda (cc) (set! fail (lambda () (begin (set! i (+ i 1)) (cc (- 1)))))))
                              (if (eqv? i m)
                                  (begin (set! fail last) (fail))
                                  (f i)))))))
                   (fun choose (lambda () (fail))))))))

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
