; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "records")

(DEFUN SUBSET (X Y)
       (IF (ENDP X)
           'T
           (IF (MEMBERP (CAR X) Y)
               (SUBSET (CDR X) Y)
               'NIL)))

(DEFUN SET-INTERSECT (X Y)
       (IF (ENDP X)
           'NIL
           (IF (MEMBERP (CAR X) Y)
               (CONS (CAR X) (SET-INTERSECT (CDR X) Y))
               (SET-INTERSECT (CDR X) Y))))

(DEFUN SET-UNION (X Y)
       (IF (ENDP X)
           Y
           (IF (MEMBERP (CAR X) Y)
               (SET-UNION (CDR X) Y)
               (CONS (CAR X) (SET-UNION (CDR X) Y)))))

(DEFUN SET-EQUAL (X Y) (IF (SUBSET X Y) (SUBSET Y X) 'NIL))

(DEFTHM SUBSET-IS-REFLEXIVE (SUBSET X X))

(DEFTHM SUBSET-IS-TRANSITIVE
        (IMPLIES (IF (SUBSET X Y) (SUBSET Y Z) 'NIL)
                 (SUBSET X Z)))

(DEFTHM SUBSET-OF-EMPTY-IS-EMPTY
        (IMPLIES (IF (NOT (CONSP X)) (SUBSET Y X) 'NIL)
                 (NOT (CONSP Y))))

(DEFTHM SET-EQUAL-IS-AN-EQUIVALENCE
        (IF (BOOLEANP (SET-EQUAL X Y))
            (IF (SET-EQUAL X X)
                (IF (IMPLIES (SET-EQUAL X Y)
                             (SET-EQUAL Y X))
                    (IMPLIES (IF (SET-EQUAL X Y)
                                 (SET-EQUAL Y Z)
                                 'NIL)
                             (SET-EQUAL X Z))
                    'NIL)
                'NIL)
            'NIL))

(DEFTHM SUBSET-IS-ANTISYMMETRIC
        (IMPLIES (IF (SUBSET X Y) (SUBSET Y X) 'NIL)
                 (SET-EQUAL X Y)))

(DEFTHM INTERSECT-IS-A-SUBSET-1 (SUBSET (SET-INTERSECT X Y) X))

(DEFTHM INTERSECT-IS-A-SUBSET-2 (SUBSET (SET-INTERSECT X Y) Y))

(DEFTHM UNION-IS-A-SUBSET-1 (SUBSET X (SET-UNION X Y)))

(DEFTHM UNION-IS-A-SUBSET-2 (SUBSET Y (SET-UNION X Y)))

(DEFTHM SUPERSET-CONTAINS-EVERYTHING
        (IMPLIES (IF (MEMBERP E X) (SUBSET X Y) 'NIL)
                 (MEMBERP E Y)))

(DEFTHM SUBSET-OF-NIL-IS-NIL
        (IMPLIES (IF (NOT (CONSP Y)) (SUBSET X Y) 'NIL)
                 (NOT (CONSP X))))

(DEFUN PROPER-SUBSET (X Y) (IF (SUBSET X Y) (NOT (SUBSET Y X)) 'NIL))

(DEFTHM PROPER-SUBSET-IS-IRREFLEXIVE (NOT (PROPER-SUBSET X X)))

(DEFTHM PROPER-SUBSET-IS-TRANSITIVE
        (IMPLIES (IF (PROPER-SUBSET X Y)
                     (PROPER-SUBSET Y Z)
                     'NIL)
                 (PROPER-SUBSET X Z)))

(DEFTHM PROPER-SUBSET-IS-STRONGER-THAN-SUBSET
        (IMPLIES (PROPER-SUBSET X Y)
                 (SUBSET X Y)))
