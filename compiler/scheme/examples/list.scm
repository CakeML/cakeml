(letrec (
  (cons (lambda (car cdr) (lambda (b) (if b car cdr))))
  (car (lambda (cons) (cons #t)))
  (cdr (lambda (cons) (cons #f)))
  (nil 999)
  (nil? (lambda (l) (eqv? l nil)))
  (length (lambda (l) (if (nil? l) 0 (+ 1 (length (cdr l))))))
  (index (lambda (n l) (if (eqv? n 0) (car l) (index (- n 1) (cdr l)))))
) (index 1 (cons 10 (cons 20 (cons 30 nil)))))
