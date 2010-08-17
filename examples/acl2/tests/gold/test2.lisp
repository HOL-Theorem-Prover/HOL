; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(DEFUN FOO (X) (CONS X X))

(DEFTHM FOO-PROP (EQUAL (CAR (FOO X)) X))

(MUTUAL-RECURSION (DEFUN BAR (X)
                         (IF (CONSP X) (BAR (CDR X)) X))
                  (DEFUN H (X) X))
