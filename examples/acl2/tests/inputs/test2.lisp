; A trivial test, but with macros called in bodies and some stuff that should
; be ignored.

(in-package "ACL2")

(defmacro my-cons (x y)
  `(cons ,x ,y))

(defun foo (x)
  (my-cons x x)) ; macro call

(defthm foo-prop
  (equal (first (foo x)) ; macro call
         x))

(set-bogus-mutual-recursion-ok t) ; should be ignored for translation

(mutual-recursion
 (defun bar (x)
   (declare (xargs :measure (acl2-count x))) ; should be ignored for translation
   (if (consp x)
       (bar (cdr x))
     x))
 (defun h (x)
   x))
