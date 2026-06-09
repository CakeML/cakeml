(letrec
    ; no quotes yet, so '() or null has to be written as ((lambda x x))
    ((null ((lambda x x)))
     (length
      (lambda (x)
          (if (null? x) 0
              (+ 1 (length (cdr x))))))
     (el
      (lambda (i x)
          (if (eqv? i 0)
              (car x)
              (el (- i 1) (cdr x)))))
     (map
      (lambda (f x)
          (if (null? x) x
              (cons (f (car x)) (map f (cdr x))))))
     (foldl
      (lambda (f e x)
          (if (null? x) e
              (foldl f (f e (car x)) (cdr x)))))
     (append
      (lambda (x y)
          (if (null? x) y
              (cons (car x) (append (cdr x) y)))))
     (cat (lambda (x) (foldl append null x))))
    ((lambda y
        ((lambda x
             (el 9 (cat (cons x (cons y (cons y (cons x null)))))))
             1 2 3))
         9 8 7))
