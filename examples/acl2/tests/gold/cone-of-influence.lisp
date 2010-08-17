; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "circuits")

(DEFUN FIND-VARIABLES* (EQUATION-LIST)
       (IF (ENDP EQUATION-LIST)
           'NIL
           (SET-UNION (FIND-VARIABLES (CAR EQUATION-LIST))
                      (FIND-VARIABLES* (CDR EQUATION-LIST)))))

(DEFUN FIND-ALL-VARIABLES-1-PASS
       (VARS EQUATIONS)
       (IF (ENDP VARS)
           'NIL
           (SET-UNION (FIND-VARIABLES* (G (CAR VARS) EQUATIONS))
                      (FIND-ALL-VARIABLES-1-PASS (CDR VARS)
                                                 EQUATIONS))))

(DEFUN DEL (E X)
       (IF (ENDP X)
           X
           (IF (EQUAL E (CAR X))
               (CDR X)
               (CONS (CAR X) (DEL E (CDR X))))))

(DEFUN INDUCTION-HINT-FOR-LEN-<= (X Y)
       (IF (ENDP X)
           (CONS X (CONS Y 'NIL))
           (INDUCTION-HINT-FOR-LEN-<= (CDR X)
                                      (DEL (CAR X) Y))))

(DEFUN
    FIND-ALL-VARIABLES
    (VARS VARIABLES EQUATIONS)
    (IF (IF (NOT (UNIQUEP VARIABLES))
            (NOT (UNIQUEP VARIABLES))
            (IF (NOT (UNIQUEP VARS))
                (NOT (UNIQUEP VARS))
                (NOT (SUBSET VARS VARIABLES))))
        VARS
        ((LAMBDA (NEW-VARS EQUATIONS VARS VARIABLES)
                 (IF (NOT (SUBSET NEW-VARS VARIABLES))
                     'NIL
                     (IF (SET-EQUAL VARS NEW-VARS)
                         VARS
                         (FIND-ALL-VARIABLES NEW-VARS VARIABLES EQUATIONS))))
         (SET-UNION (FIND-ALL-VARIABLES-1-PASS VARS EQUATIONS)
                    VARS)
         EQUATIONS VARS VARIABLES)))

(DEFUN FIND-ALL-EQUATIONS
       (VARS EQUATIONS EQ-REC)
       (IF (ENDP VARS)
           EQ-REC
           (FIND-ALL-EQUATIONS (CDR VARS)
                               EQUATIONS
                               (S (CAR VARS)
                                  (G (CAR VARS) EQUATIONS)
                                  EQ-REC))))

(DEFUN REMOVE-DUPLICATE-OCCURRENCES (X)
       (IF (ENDP X)
           X
           (IF (MEMBERP (CAR X) (CDR X))
               (REMOVE-DUPLICATE-OCCURRENCES (CDR X))
               (CONS (CAR X)
                     (REMOVE-DUPLICATE-OCCURRENCES (CDR X))))))

(DEFUN CORRESPONDING-STATE (INIT VARS)
       (IF (ENDP VARS)
           'NIL
           (S (CAR VARS)
              (G (CAR VARS) INIT)
              (CORRESPONDING-STATE INIT (CDR VARS)))))

(DEFUN CORRESPONDING-STATES (INITS VARS)
       (IF (ENDP INITS)
           'NIL
           (CONS (CORRESPONDING-STATE (CAR INITS) VARS)
                 (CORRESPONDING-STATES (CDR INITS)
                                       VARS))))

(DEFUN CONE-VARIABLES (VARS C)
       (FIND-ALL-VARIABLES (SET-INTERSECT (REMOVE-DUPLICATE-OCCURRENCES VARS)
                                          (G ':VARIABLES C))
                           (G ':VARIABLES C)
                           (G ':EQUATIONS C)))

(DEFUN CONE-OF-INFLUENCE-REDUCTION (C VARS)
       ((LAMBDA (VARIABLES C)
                (S ':EQUATIONS
                   (FIND-ALL-EQUATIONS VARIABLES (G ':EQUATIONS C)
                                       'NIL)
                   (S ':INITIAL-STATES
                      (CORRESPONDING-STATES (G ':INITIAL-STATES C)
                                            VARIABLES)
                      (S ':VARIABLES VARIABLES 'NIL))))
        (CONE-VARIABLES VARS C)
        C))

(DEFTHM
   EVALUATION-EQ-MEMBERP-FROM-ALL-EVALUATIONS-P
   (IMPLIES
        (IF (ALL-EVALUATIONS-P STATES-CONE VARS-CONE)
            (IF (EVALUATION-P S VARS-CONE)
                (IF (CONSISTENT-P-EQUATIONS VARS-CONE EQN EQUATIONS-CONE)
                    (EVALUATION-EQ S (PRODUCE-NEXT-STATE VARS-CONE Q EQN)
                                   VARS-CONE)
                    'NIL)
                'NIL)
            'NIL)
        (EVALUATION-EQ-MEMBER-P
             S
             (CREATE-NEXT-STATES-OF-P Q STATES-CONE VARS-CONE EQUATIONS-CONE)
             VARS-CONE)))

(DEFTHM CONE-OF-INFLUENCE-REDUCTION-IS-CIRCUIT-P
        (IMPLIES (CIRCUITP C)
                 (CIRCUITP (CONE-OF-INFLUENCE-REDUCTION C VARS))))

(DEFTHM
 CONE-OF-INFLUENCE-IS-C-BISIMI-EQUIV
 (IMPLIES (CIRCUITP C)
          (C-BISIM-EQUIV (CREATE-KRIPKE C)
                         (CREATE-KRIPKE (CONE-OF-INFLUENCE-REDUCTION C VARS))
                         (CONE-VARIABLES VARS C))))
