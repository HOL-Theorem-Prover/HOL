; A trivial test

(in-package "ACL2")

(defun foo (x)
  (cons x x))

(defthm foo-prop
  (equal (car (foo x))
         x))

(progn
  (defun bar (x)
    (foo x))
  (defun h (x)
    (bar x)))
