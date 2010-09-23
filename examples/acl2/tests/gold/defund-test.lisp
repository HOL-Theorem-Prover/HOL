(IN-PACKAGE "ACL2")

(DEFUN FOO (X) X)

(DEFUN BAR (X) X)

(MUTUAL-RECURSION (DEFUN EVENLP (X)
                         (IF (CONSP X) (ODDLP (CDR X)) 'T))
                  (DEFUN ODDLP (X)
                         (IF (CONSP X) (EVENLP (CDR X)) 'NIL)))

(MUTUAL-RECURSION (DEFUN EVENLP2 (X)
                         (PROG2$ (THROW-NONEXEC-ERROR 'EVENLP2
                                                      (CONS X 'NIL))
                                 (IF (CONSP X) (ODDLP2 (CDR X)) 'T)))
                  (DEFUN ODDLP2 (X)
                         (PROG2$ (THROW-NONEXEC-ERROR 'ODDLP2
                                                      (CONS X 'NIL))
                                 (IF (CONSP X) (EVENLP2 (CDR X)) 'NIL))))
