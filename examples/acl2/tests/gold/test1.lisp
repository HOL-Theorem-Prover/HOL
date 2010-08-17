; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(DEFUN FOO (X) (CONS X X))

(DEFTHM FOO-PROP (EQUAL (CAR (FOO X)) X))

(DEFUN BAR (X) (FOO X))

(DEFUN H (X) (BAR X))
