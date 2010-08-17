; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(DEFTHM CAR-CONS-1 (EQUAL (CAR (CONS X Y)) X))

(DEFTHM CAR-CONS-2 (EQUAL (CAR (CONS X Y)) X))

(DEFUN F1 (X) X)

(DEFTHM CAR-CONS-3 (EQUAL (CAR (CONS X Y)) X))

(DEFUN F2 (X) X)

(ENCAP ((G1 1)) (DEFTHM INTEGERP-G1 (INTEGERP (G1 X))))

(ENCAP ((G2 1)) (DEFTHM INTEGERP-FIRST-G2 (INTEGERP (MV-NTH '0 (G2 X)))))

(ENCAP ((H1 1) (H2 2))
       (DEFTHM H1-PROP
               (IMPLIES (INTEGERP X)
                        (INTEGERP (H1 X))))
       (DEFTHM H2-PROP
               (IMPLIES (INTEGERP Y)
                        (INTEGERP (MV-NTH '0 (H2 X Y))))))

(ENCAP ((H3 1) (H4 2))
       (DEFTHM H3-PROP
               (IMPLIES (INTEGERP X)
                        (INTEGERP (H3 X))))
       (DEFUN H5 (X) (H3 X))
       (DEFTHM H4-H5-PROP
               (IMPLIES (INTEGERP Y)
                        (INTEGERP (H5 (MV-NTH '0 (H4 X Y)))))))
