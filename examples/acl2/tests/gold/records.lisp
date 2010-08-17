; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "apply-total-order")

(DEFUN RCDP (X)
       (IF (NULL X)
           (NULL X)
           (IF (CONSP X)
               (IF (CONSP (CAR X))
                   (IF (RCDP (CDR X))
                       (IF (CDR (CAR X))
                           (IF (NULL (CDR X))
                               (NULL (CDR X))
                               (<< (CAR (CAR X)) (CAR (CAR (CDR X)))))
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN IFRP (X)
       (IF (NOT (RCDP X))
           (NOT (RCDP X))
           (IF (CONSP X)
               (IF (NULL (CDR X))
                   (IF (CONSP (CAR X))
                       (IF (NULL (CAR (CAR X)))
                           (IFRP (CDR (CAR X)))
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN ACL2->RCD (X) (IF (IFRP X) (CONS (CONS 'NIL X) 'NIL) X))

(DEFUN RCD->ACL2 (X) (IF (IFRP X) (CDR (CAR X)) X))

(DEFUN G-AUX (A X)
       (IF (IF (ENDP X)
               (ENDP X)
               (<< A (CAR (CAR X))))
           'NIL
           (IF (EQUAL A (CAR (CAR X)))
               (CDR (CAR X))
               (G-AUX A (CDR X)))))

(DEFUN G (A X) (G-AUX A (ACL2->RCD X)))

(DEFUN S-AUX (A V R)
       (IF (IF (ENDP R)
               (ENDP R)
               (<< A (CAR (CAR R))))
           (IF V (CONS (CONS A V) R) R)
           (IF (EQUAL A (CAR (CAR R)))
               (IF V (CONS (CONS A V) (CDR R)) (CDR R))
               (CONS (CAR R) (S-AUX A V (CDR R))))))

(DEFUN S (A V X) (RCD->ACL2 (S-AUX A V (ACL2->RCD X))))

(DEFUN KEYS-AUX (X)
       (IF (ENDP X)
           'NIL
           (CONS (CAR (CAR X))
                 (KEYS-AUX (CDR X)))))

(DEFUN KEYS (X) (KEYS-AUX (ACL2->RCD X)))

(DEFTHM G-SAME-S (EQUAL (G A (S A V R)) V))

(DEFTHM G-DIFF-S
        (IMPLIES (NOT (EQUAL A B))
                 (EQUAL (G A (S B V R)) (G A R))))

(DEFTHM G-OF-S-REDUX (EQUAL (G A (S B V R)) (IF (EQUAL A B) V (G A R))))

(DEFTHM S-SAME-G (EQUAL (S A (G A R) R) R))

(DEFTHM S-SAME-S (EQUAL (S A Y (S A X R)) (S A Y R)))

(DEFTHM S-DIFF-S
        (IMPLIES (NOT (EQUAL A B))
                 (EQUAL (S B Y (S A X R))
                        (S A X (S B Y R)))))

(DEFTHM G-KEYS-RELATIONSHIP (IFF (MEMBERP A (KEYS R)) (G A R)))

(DEFTHM S-KEYS-REDUCTION
        (EQUAL (KEYS (S A V R))
               (IF V (INSERT A (KEYS R))
                   (DROP A (KEYS R)))))

(DEFTHM KEYS-ARE-ORDERED (ORDEREDP (KEYS R)))

(DEFTHM G-OF-NIL-IS-NIL (NOT (G A 'NIL)))

(DEFTHM S-NON-NIL-CANNOT-BE-NIL (IMPLIES V (S A V R)))

(DEFTHM NON-NIL-IF-G-NON-NIL (IMPLIES (G A R) R))

(DEFTHM S-SAME-G-BACK-CHAINING
        (IMPLIES (EQUAL V (G A R))
                 (EQUAL (S A V R) R)))

(DEFUN UPDATE-MACRO (UPDS RESULT)
       (IF (ENDP UPDS)
           RESULT
           (UPDATE-MACRO (CDR (CDR UPDS))
                         (CONS 'S
                               (CONS (CAR UPDS)
                                     (CONS (CAR (CDR UPDS))
                                           (CONS RESULT 'NIL)))))))
