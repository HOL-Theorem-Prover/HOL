(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "sets")

(DEFUN LTL-CONSTANTP (F)
       (IF (EQUAL F 'TRUE)
           (EQUAL F 'TRUE)
           (EQUAL F 'FALSE)))

(DEFUN LTL-VARIABLEP (F)
       (IF (SYMBOLP F)
           (NOT (MEMBERP F '(+ & U W X F G)))
           'NIL))

(DEFUN LTL-FORMULAP (F)
       (IF (ATOM F)
           (IF (LTL-CONSTANTP F)
               (LTL-CONSTANTP F)
               (LTL-VARIABLEP F))
           (IF (EQUAL (LEN F) '3)
               (IF (MEMBERP (CAR (CDR F)) '(+ & U W))
                   (IF (LTL-FORMULAP (CAR F))
                       (LTL-FORMULAP (CAR (CDR (CDR F))))
                       'NIL)
                   'NIL)
               (IF (EQUAL (LEN F) '2)
                   (IF (MEMBERP (CAR F) '(~ X F G))
                       (LTL-FORMULAP (CAR (CDR F)))
                       'NIL)
                   'NIL))))

(DEFUN RESTRICTED-FORMULAP (F V-LIST)
       (IF (ATOM F)
           (IF (LTL-CONSTANTP F)
               (LTL-CONSTANTP F)
               (IF (LTL-VARIABLEP F)
                   (MEMBERP F V-LIST)
                   'NIL))
           (IF (EQUAL (LEN F) '3)
               (IF (MEMBERP (CAR (CDR F)) '(& + U W))
                   (IF (RESTRICTED-FORMULAP (CAR F) V-LIST)
                       (RESTRICTED-FORMULAP (CAR (CDR (CDR F)))
                                            V-LIST)
                       'NIL)
                   'NIL)
               (IF (EQUAL (LEN F) '2)
                   (IF (MEMBERP (CAR F) '(~ X F G))
                       (RESTRICTED-FORMULAP (CAR (CDR F))
                                            V-LIST)
                       'NIL)
                   'NIL))))

(DEFTHM RESTRICTED-FORMULA-IS-AN-LTL-FORMULA
        (IMPLIES (RESTRICTED-FORMULAP F V-LIST)
                 (LTL-FORMULAP F)))

(DEFUN CREATE-RESTRICTED-VAR-SET (F)
       (IF (ATOM F)
           (IF (LTL-CONSTANTP F)
               'NIL
               (CONS F 'NIL))
           (IF (EQUAL (LEN F) '3)
               (SET-UNION (CREATE-RESTRICTED-VAR-SET (CAR F))
                          (CREATE-RESTRICTED-VAR-SET (CAR (CDR (CDR F)))))
               (IF (EQUAL (LEN F) '2)
                   (CREATE-RESTRICTED-VAR-SET (CAR (CDR F)))
                   'NIL))))

(DEFTHM LTL-FORMULA-IS-A-RESTRICTED-FORMULA
        (IMPLIES (LTL-FORMULAP F)
                 (RESTRICTED-FORMULAP F (CREATE-RESTRICTED-VAR-SET F))))

(DEFUN NEXT-STATEP (P Q M) (MEMBERP Q (G P (G ':TRANSITION M))))

(DEFUN INITIAL-STATEP (P M) (MEMBERP P (G ':INITIAL-STATES M)))

(DEFUN LABEL-OF (S M) (G S (G ':LABEL-FN M)))

(DEFUN NEXT-STATES-IN-STATES (M STATES)
       (IF (ENDP STATES)
           'T
           (IF (SUBSET (G (CAR STATES) (G ':TRANSITION M))
                       (G ':STATES M))
               (NEXT-STATES-IN-STATES M (CDR STATES))
               'NIL)))

(DEFTHM NEXT-STATES-IN-STATES-CLARIFIED-AUX
        (IMPLIES (IF (MEMBERP P STATES)
                     (IF (NEXT-STATES-IN-STATES M STATES)
                         (NEXT-STATEP P Q M)
                         'NIL)
                     'NIL)
                 (MEMBERP Q (G ':STATES M))))

(DEFTHM NEXT-STATES-IN-STATES-CLARIFIED
        (IMPLIES (IF (NEXT-STATES-IN-STATES M (G ':STATES M))
                     (IF (MEMBERP P (G ':STATES M))
                         (NEXT-STATEP P Q M)
                         'NIL)
                     'NIL)
                 (MEMBERP Q (G ':STATES M))))
