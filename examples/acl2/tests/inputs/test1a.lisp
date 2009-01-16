; Like test1.lisp, but one big progn, and with a local event (which should be
; skipped).

(in-package "ACL2")

(progn

(defun foo (x)
  (cons x x))

(local (defun g (x) x))

(defthm foo-prop
  (equal (car (foo x))
         x))

(progn
  (defun bar (x)
    (foo x))
  (defun h (x)
    (bar x)))

)
