(in-package "MY-PKG")

(defun f1 (x)
  (cons x x))

(defun f2 (x)
  (acl2::append x x))
