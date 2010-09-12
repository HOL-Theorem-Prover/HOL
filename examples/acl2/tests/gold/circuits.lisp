(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "circuit-bisim")

(DEFUN FIND-VARIABLES (EQUATION)
       (IF (IF (ATOM EQUATION)
               (NOT (BOOLEANP EQUATION))
               'NIL)
           (CONS EQUATION 'NIL)
           (IF (IF (EQUAL (LEN EQUATION) '3)
                   (MEMBERP (CAR (CDR EQUATION)) '(& +))
                   'NIL)
               (SET-UNION (FIND-VARIABLES (CAR EQUATION))
                          (FIND-VARIABLES (CAR (CDR (CDR EQUATION)))))
               (IF (IF (EQUAL (LEN EQUATION) '2)
                       (EQUAL (CAR EQUATION) '~)
                       'NIL)
                   (FIND-VARIABLES (CAR (CDR EQUATION)))
                   'NIL))))

(DEFUN-SK CONSISTENT-EQUATION-RECORD-P
          (VARS EQUATIONS)
          (FORALL (V EQUATION)
                  (IMPLIES (IF (UNIQUEP VARS)
                               (IF (MEMBERP V VARS)
                                   (MEMBERP EQUATION (G V EQUATIONS))
                                   'NIL)
                               'NIL)
                           (SUBSET (FIND-VARIABLES EQUATION)
                                   VARS))))

(DEFUN CONS-LIST-P (VARS EQUATIONS)
       (IF (ENDP VARS)
           'T
           (IF (CONSP (G (CAR VARS) EQUATIONS))
               (CONS-LIST-P (CDR VARS) EQUATIONS)
               'NIL)))

(DEFUN CIRCUITP (C)
       (IF (ONLY-EVALUATIONS-P (G ':INITIAL-STATES C)
                               (G ':VARIABLES C))
           (IF (STRICT-EVALUATION-LIST-P (G ':VARIABLES C)
                                         (G ':INITIAL-STATES C))
               (IF (UNIQUEP (G ':VARIABLES C))
                   (IF (CONS-LIST-P (G ':VARIABLES C)
                                    (G ':EQUATIONS C))
                       (CONSISTENT-EQUATION-RECORD-P (G ':VARIABLES C)
                                                     (G ':EQUATIONS C))
                       'NIL)
                   'NIL)
               'NIL)
           'NIL))

(DEFUN ASSIGN-T (V STATES)
       (IF (ENDP STATES)
           'NIL
           (CONS (S V 'T (CAR STATES))
                 (ASSIGN-T V (CDR STATES)))))

(DEFUN ASSIGN-NIL (V STATES)
       (IF (ENDP STATES)
           'NIL
           (CONS (S V 'NIL (CAR STATES))
                 (ASSIGN-NIL V (CDR STATES)))))

(DEFUN CREATE-ALL-EVALUATIONS (VARS STATES)
       (IF (ENDP VARS)
           STATES
           ((LAMBDA (REC-STATES VARS)
                    (BINARY-APPEND (ASSIGN-T (CAR VARS) REC-STATES)
                                   (ASSIGN-NIL (CAR VARS) REC-STATES)))
            (CREATE-ALL-EVALUATIONS (CDR VARS)
                                    STATES)
            VARS)))

(DEFUN LABEL-FN-OF-ST (ST VARS)
       (IF (ENDP VARS)
           'NIL
           (IF (EQUAL (G (CAR VARS) ST) 'T)
               (CONS (CAR VARS)
                     (LABEL-FN-OF-ST ST (CDR VARS)))
               (LABEL-FN-OF-ST ST (CDR VARS)))))

(DEFUN CREATE-LABEL-FN (STATES VARS LABEL)
       (IF (ENDP STATES)
           LABEL
           (CREATE-LABEL-FN (CDR STATES)
                            VARS
                            (S (CAR STATES)
                               (LABEL-FN-OF-ST (CAR STATES) VARS)
                               LABEL))))

(DEFUN
  APPLY-EQUATION (EQUATION ST)
  (IF (ATOM EQUATION)
      (IF (BOOLEANP EQUATION)
          EQUATION (G EQUATION ST))
      (IF (EQUAL (LEN EQUATION) '2)
          ((LAMBDA (CASE-DO-NOT-USE-ELSEWHERE ST EQUATION)
                   (IF (EQL CASE-DO-NOT-USE-ELSEWHERE '~)
                       (NOT (APPLY-EQUATION (CAR (CDR EQUATION))
                                            ST))
                       'NIL))
           (CAR EQUATION)
           ST EQUATION)
          (IF (EQUAL (LEN EQUATION) '3)
              ((LAMBDA (CASE-DO-NOT-USE-ELSEWHERE ST EQUATION)
                       (IF (EQL CASE-DO-NOT-USE-ELSEWHERE '&)
                           (IF (APPLY-EQUATION (CAR EQUATION) ST)
                               (APPLY-EQUATION (CAR (CDR (CDR EQUATION)))
                                               ST)
                               'NIL)
                           (IF (EQL CASE-DO-NOT-USE-ELSEWHERE '+)
                               (IF (APPLY-EQUATION (CAR EQUATION) ST)
                                   (APPLY-EQUATION (CAR EQUATION) ST)
                                   (APPLY-EQUATION (CAR (CDR (CDR EQUATION)))
                                                   ST))
                               'NIL)))
               (CAR (CDR EQUATION))
               ST EQUATION)
              'NIL))))

(DEFUN PRODUCE-NEXT-STATE (VARS ST EQUATIONS)
       (IF (ENDP VARS)
           ST
           (S (CAR VARS)
              (APPLY-EQUATION (G (CAR VARS) EQUATIONS)
                              ST)
              (PRODUCE-NEXT-STATE (CDR VARS)
                                  ST EQUATIONS))))

(DEFUN CONSISTENT-P-EQUATIONS
       (VARS EQN EQUATIONS)
       (IF (ENDP VARS)
           'T
           (IF (MEMBERP (G (CAR VARS) EQN)
                        (G (CAR VARS) EQUATIONS))
               (CONSISTENT-P-EQUATIONS (CDR VARS)
                                       EQN EQUATIONS)
               'NIL)))

(DEFUN-SK NEXT-STATE-IS-OK (P Q VARS EQUATIONS)
          (EXISTS (EQN)
                  (IF (CONSISTENT-P-EQUATIONS VARS EQN EQUATIONS)
                      (EVALUATION-EQ Q (PRODUCE-NEXT-STATE VARS P EQN)
                                     VARS)
                      'NIL)))

(DEFUN CREATE-NEXT-STATES-OF-P
       (P STATES VARS EQUATIONS)
       (IF (ENDP STATES)
           'NIL
           (IF (NEXT-STATE-IS-OK P (CAR STATES)
                                 VARS EQUATIONS)
               (CONS (CAR STATES)
                     (CREATE-NEXT-STATES-OF-P P (CDR STATES)
                                              VARS EQUATIONS))
               (CREATE-NEXT-STATES-OF-P P (CDR STATES)
                                        VARS EQUATIONS))))

(DEFUN CREATE-NEXT-STATES
       (STATES STATES-PRIME VARS EQUATIONS)
       (IF (ENDP STATES)
           'NIL
           (S (CAR STATES)
              (CREATE-NEXT-STATES-OF-P (CAR STATES)
                                       STATES-PRIME VARS EQUATIONS)
              (CREATE-NEXT-STATES (CDR STATES)
                                  STATES-PRIME VARS EQUATIONS))))

(DEFUN
 CREATE-KRIPKE (C)
 ((LAMBDA
     (VARS EQUATIONS INITIAL-STATES)
     ((LAMBDA
           (STATES EQUATIONS VARS INITIAL-STATES)
           ((LAMBDA (LABEL-FN EQUATIONS VARS STATES INITIAL-STATES)
                    ((LAMBDA (TRANSITION STATES INITIAL-STATES LABEL-FN VARS)
                             (S ':VARIABLES
                                VARS
                                (S ':TRANSITION
                                   TRANSITION
                                   (S ':LABEL-FN
                                      LABEL-FN
                                      (S ':INITIAL-STATES
                                         INITIAL-STATES
                                         (S ':STATES
                                            (SET-UNION INITIAL-STATES STATES)
                                            'NIL))))))
                     (CREATE-NEXT-STATES (SET-UNION INITIAL-STATES STATES)
                                         (SET-UNION INITIAL-STATES STATES)
                                         VARS EQUATIONS)
                     STATES INITIAL-STATES LABEL-FN VARS))
            (CREATE-LABEL-FN (SET-UNION INITIAL-STATES STATES)
                             VARS 'NIL)
            EQUATIONS VARS STATES INITIAL-STATES))
      (CREATE-ALL-EVALUATIONS VARS (CONS 'NIL 'NIL))
      EQUATIONS VARS INITIAL-STATES))
  (G ':VARIABLES C)
  (G ':EQUATIONS C)
  (G ':INITIAL-STATES C)))

(DEFTHM CREATE-KRIPKE-PRODUCES-CIRCUIT-MODEL
        (IMPLIES (CIRCUITP C)
                 (CIRCUIT-MODELP (CREATE-KRIPKE C))))
