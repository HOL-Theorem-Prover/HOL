(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "total-order")

(DEFUN MEMBERP (A X)
       (IF (CONSP X)
           (IF (EQUAL A (CAR X))
               (EQUAL A (CAR X))
               (MEMBERP A (CDR X)))
           'NIL))

(DEFUN DROP (A X)
       (IF (ENDP X)
           'NIL
           (IF (EQUAL A (CAR X))
               (DROP A (CDR X))
               (CONS (CAR X) (DROP A (CDR X))))))

(DEFUN INSERT (A X)
       (IF (ENDP X)
           (CONS A 'NIL)
           (IF (EQUAL A (CAR X))
               X
               (IF (<< A (CAR X))
                   (CONS A X)
                   (CONS (CAR X) (INSERT A (CDR X)))))))

(DEFUN ORDEREDP (X)
       (IF (ENDP (CDR X))
           (ENDP (CDR X))
           (IF (<< (CAR X) (CAR (CDR X)))
               (ORDEREDP (CDR X))
               'NIL)))

(DEFUN UNIQUEP (X)
       (IF (ENDP X)
           (ENDP X)
           (IF (NOT (MEMBERP (CAR X) (CDR X)))
               (UNIQUEP (CDR X))
               'NIL)))

(DEFTHM MEMBERP-INSERT-SAME (EQUAL (MEMBERP A (INSERT A X)) 'T))

(DEFTHM MEMBERP-INSERT-DIFF
        (IMPLIES (NOT (EQUAL A B))
                 (EQUAL (MEMBERP A (INSERT B X))
                        (MEMBERP A X))))

(DEFTHM MEMBERP-DROP-SAME (EQUAL (MEMBERP A (DROP A X)) 'NIL))

(DEFTHM MEMBERP-DROP-DIFF
        (IMPLIES (NOT (EQUAL A B))
                 (EQUAL (MEMBERP A (DROP B X))
                        (MEMBERP A X))))

(DEFTHM ORDERED-IMPLIES-UNIQUE (IMPLIES (ORDEREDP X) (UNIQUEP X)))

(DEFTHM MEMBERP-YES-REDUCE-INSERT
        (IMPLIES (IF (ORDEREDP X) (MEMBERP A X) 'NIL)
                 (EQUAL (INSERT A X) X)))

(DEFTHM MEMBERP-NO-REDUCE-DROP
        (IMPLIES (IF (TRUE-LISTP X)
                     (NOT (MEMBERP A X))
                     'NIL)
                 (EQUAL (DROP A X) X)))

(DEFTHM DROP-PRESERVES-ORDEREDP
        (IMPLIES (ORDEREDP X)
                 (ORDEREDP (DROP A X))))

(DEFTHM INSERT-PRESERVES-ORDEREDP
        (IMPLIES (ORDEREDP X)
                 (ORDEREDP (INSERT A X))))

(DEFTHM DROP-OF-INSERT-IS-SAME
        (IMPLIES (IF (TRUE-LISTP X)
                     (NOT (MEMBERP A X))
                     'NIL)
                 (EQUAL (DROP A (INSERT A X)) X)))

(DEFTHM INSERT-OF-DROP-IS-SAME
        (IMPLIES (IF (ORDEREDP X)
                     (IF (TRUE-LISTP X) (MEMBERP A X) 'NIL)
                     'NIL)
                 (EQUAL (INSERT A (DROP A X)) X)))

(DEFTHM INSERT-RETURNS-TRUE-LISTS
        (IMPLIES (TRUE-LISTP X)
                 (TRUE-LISTP (INSERT A X))))
