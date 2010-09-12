(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "summary")

(DEFTHM RANGE-TRANSITION-RELATION
        (IMPLIES (IF (MEMBERP P (G ':STATES M))
                     (IF (NEXT-STATEP P Q M)
                         (CIRCUIT-MODELP M)
                         'NIL)
                     'NIL)
                 (MEMBERP Q (G ':STATES M))))

(DEFTHM SUBSET-IMPLIES-MEMBERP
        (IMPLIES (IF (SUBSET X Y) (MEMBERP A X) 'NIL)
                 (MEMBERP A Y)))

(DEFTHM INITIAL-STATE-IS-STATE
        (IMPLIES (IF (CIRCUIT-MODELP M)
                     (MEMBERP S0 (G ':INITIAL-STATES M))
                     'NIL)
                 (MEMBERP S0 (G ':STATES M))))

(DEFTHM MEMBERP-SET-UNION
        (EQUAL (MEMBERP A (SET-UNION X Y))
               (IF (MEMBERP A X)
                   (MEMBERP A X)
                   (MEMBERP A Y))))

(DEFTHM MEMBERP-SET-INTERSECT
        (EQUAL (MEMBERP A (SET-INTERSECT X Y))
               (IF (MEMBERP A X) (MEMBERP A Y) 'NIL)))

(DEFTHM SUBSET-PRESERVES-MEMBERP
        (IMPLIES (IF (SUBSET X Y) (MEMBERP A X) 'NIL)
                 (EQUAL (MEMBERP A Y) 'T)))

(DEFTHM SET-EQUAL-IMPLIES-EQUAL-MEMBERP
        (IMPLIES (SET-EQUAL X Y)
                 (EQUAL (EQUAL (MEMBERP A X) (MEMBERP A Y))
                        'T)))

(DEFTHM BISIM-LEMMA-1-LEMMA
        (IMPLIES (CIRCUIT-BISIM P M Q N VARS)
                 (EQUAL (MEMBERP A (SET-INTERSECT (LABEL-OF P M) VARS))
                        (MEMBERP A
                                 (SET-INTERSECT (LABEL-OF Q N) VARS)))))

(DEFTHM BISIM-LEMMA-1
        (IMPLIES (IF (MEMBERP A VARS)
                     (CIRCUIT-BISIM P M Q N VARS)
                     'NIL)
                 (EQUAL (MEMBERP A (LABEL-OF P M))
                        (MEMBERP A (LABEL-OF Q N)))))
