(in-package "ACL2")

(defund foo (x) x)

(defun bar (x) x)

; From :doc mutual-recursion, but using defund:
(mutual-recursion
 (defund evenlp (x)
   (if (consp x) (oddlp (cdr x)) t))
 (defund oddlp (x)
   (if (consp x) (evenlp (cdr x)) nil)))

; As above, but using defun-nx:
(mutual-recursion
 (defun-nx evenlp2 (x)
   (if (consp x) (oddlp2 (cdr x)) t))
 (defun-nx oddlp2 (x)
   (if (consp x) (evenlp2 (cdr x)) nil)))
