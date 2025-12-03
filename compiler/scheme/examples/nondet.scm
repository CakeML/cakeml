(letrec
    ((mklist (lambda x x))
     (nondet
      (lambda (fun)
          (call/cc
           (lambda (cc)
               (letrec ((k cc))
                   (fun
                    (lambda (l)
                         (letrec ((last k))
                             (begin
                              (call/cc
                               (lambda (cc) (set! k (lambda (v) (begin (set! l (cdr l)) (cc v))))))
                              (if (null? l)
                                  (begin (set! k last) (k (- 1)))
                                  (car l)))))
                    (lambda () (k (- 1))))))))))

     (eqv? 6 (nondet
      (lambda (choose fail)
          (letrec ((x (choose (mklist 2 4 6 8)))
                   (y (choose (mklist 3 6 9 12))))
              (if (eqv? x y) x (fail)))))))
