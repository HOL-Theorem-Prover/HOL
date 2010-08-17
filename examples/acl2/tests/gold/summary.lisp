; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "records")

(DEFUN UPDATE-MACRO (UPDS RESULT)
       (IF (ENDP UPDS)
           RESULT
           (UPDATE-MACRO (CDR (CDR UPDS))
                         (CONS 'S
                               (CONS (CAR UPDS)
                                     (CONS (CAR (CDR UPDS))
                                           (CONS RESULT 'NIL)))))))

(DEFUN MEMBERP (A X)
       (IF (CONSP X)
           (IF (EQUAL A (CAR X))
               (EQUAL A (CAR X))
               (MEMBERP A (CDR X)))
           'NIL))

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

(DEFUN EVALUATION-EQ (P Q VARS)
       (IF (ENDP VARS)
           'T
           (IF (EQUAL (G (CAR VARS) P)
                      (G (CAR VARS) Q))
               (EVALUATION-EQ P Q (CDR VARS))
               'NIL)))

(DEFUN EVALUATION-EQ-MEMBER-P (ST STATES VARS)
       (IF (ENDP STATES)
           'NIL
           (IF (EVALUATION-EQ ST (CAR STATES) VARS)
               'T
               (EVALUATION-EQ-MEMBER-P ST (CDR STATES)
                                       VARS))))

(DEFUN EVALUATION-EQ-MEMBER (ST STATES VARS)
       (IF (ENDP STATES)
           'NIL
           (IF (EVALUATION-EQ ST (CAR STATES) VARS)
               (CAR STATES)
               (EVALUATION-EQ-MEMBER ST (CDR STATES)
                                     VARS))))

(DEFUN-SK STRICT-EVALUATION-P (ST VARS)
          (FORALL (V)
                  (IMPLIES (NOT (MEMBERP V VARS))
                           (NOT (G V ST)))))

(DEFUN STRICT-EVALUATION-LIST-P (VARS STATES)
       (IF (ENDP STATES)
           'T
           (IF (STRICT-EVALUATION-P (CAR STATES) VARS)
               (STRICT-EVALUATION-LIST-P VARS (CDR STATES))
               'NIL)))

(DEFUN EVALUATION-P (ST VARS)
       (IF (ENDP VARS)
           'T
           (IF (BOOLEANP (G (CAR VARS) ST))
               (EVALUATION-P ST (CDR VARS))
               'NIL)))

(DEFUN ONLY-EVALUATIONS-P (STATES VARS)
       (IF (ENDP STATES)
           'T
           (IF (EVALUATION-P (CAR STATES) VARS)
               (ONLY-EVALUATIONS-P (CDR STATES) VARS)
               'NIL)))

(DEFUN-SK ALL-EVALUATIONS-P (STATES VARS)
          (FORALL (ST)
                  (IMPLIES (EVALUATION-P ST VARS)
                           (EVALUATION-EQ-MEMBER-P ST STATES VARS))))

(DEFUN EVALUATION-EQ-SUBSET-P
       (M-STATES N-STATES VARS)
       (IF (ENDP M-STATES)
           'T
           (IF (EVALUATION-EQ-MEMBER-P (CAR M-STATES)
                                       N-STATES VARS)
               (EVALUATION-EQ-SUBSET-P (CDR M-STATES)
                                       N-STATES VARS)
               'NIL)))

(DEFTHM EVALUATION-EQ-SUBSET-TO-MEMBER
        (IMPLIES (IF (EVALUATION-EQ-SUBSET-P M-STATES N-STATES VARS)
                     (MEMBERP P M-STATES)
                     'NIL)
                 (EVALUATION-EQ-MEMBER-P P N-STATES VARS)))

(DEFUN TRUTHP-LABEL (LABEL S)
       (IF (ENDP LABEL)
           'T
           (IF (EQUAL (G (CAR LABEL) S) 'T)
               (TRUTHP-LABEL (CDR LABEL) S)
               'NIL)))

(DEFUN ONLY-TRUTH-P (STATES M)
       (IF (ENDP STATES)
           'T
           (IF (TRUTHP-LABEL (LABEL-OF (CAR STATES) M)
                             (CAR STATES))
               (ONLY-TRUTH-P (CDR STATES) M)
               'NIL)))

(DEFUN ALL-TRUTHSP-LABEL (LABEL S VARS)
       (IF (ENDP VARS)
           'T
           (IF (IMPLIES (EQUAL (G (CAR VARS) S) 'T)
                        (MEMBERP (CAR VARS) LABEL))
               (ALL-TRUTHSP-LABEL LABEL S (CDR VARS))
               'NIL)))

(DEFUN ONLY-ALL-TRUTHS-P (STATES M VARS)
       (IF (ENDP STATES)
           'T
           (IF (ALL-TRUTHSP-LABEL (LABEL-OF (CAR STATES) M)
                                  (CAR STATES)
                                  VARS)
               (ONLY-ALL-TRUTHS-P (CDR STATES) M VARS)
               'NIL)))

(DEFUN LABEL-SUBSET-VARS (STATES M VARS)
       (IF (ENDP STATES)
           'T
           (IF (SUBSET (LABEL-OF (CAR STATES) M) VARS)
               (LABEL-SUBSET-VARS (CDR STATES) M VARS)
               'NIL)))

(DEFUN-SK WELL-FORMED-TRANSITION-P
          (STATES-M TRANS-M STATES-N TRANS-N VARS)
          (FORALL (P Q)
                  (IMPLIES (IF (EVALUATION-EQ P Q VARS)
                               (IF (EVALUATION-P P VARS)
                                   (IF (MEMBERP P STATES-M)
                                       (IF (MEMBERP Q STATES-N)
                                           (EVALUATION-P Q VARS)
                                           'NIL)
                                       'NIL)
                                   'NIL)
                               'NIL)
                           (EVALUATION-EQ-SUBSET-P (G P TRANS-M)
                                                   (G Q TRANS-N)
                                                   VARS))))

(DEFUN TRANSITION-SUBSET-P
       (STATES STATES-PRIME TRANS)
       (IF (ENDP STATES)
           'T
           (IF (SUBSET (G (CAR STATES) TRANS)
                       STATES-PRIME)
               (TRANSITION-SUBSET-P (CDR STATES)
                                    STATES-PRIME TRANS)
               'NIL)))

(DEFUN
 CIRCUIT-MODELP (M)
 (IF (ONLY-EVALUATIONS-P (G ':STATES M)
                         (G ':VARIABLES M))
     (IF (ALL-EVALUATIONS-P (G ':STATES M)
                            (G ':VARIABLES M))
         (IF (STRICT-EVALUATION-LIST-P (G ':VARIABLES M)
                                       (G ':STATES M))
             (IF (ONLY-ALL-TRUTHS-P (G ':STATES M)
                                    M (G ':VARIABLES M))
                 (IF (ONLY-TRUTH-P (G ':STATES M) M)
                     (IF (LABEL-SUBSET-VARS (G ':STATES M)
                                            M (G ':VARIABLES M))
                         (IF (TRANSITION-SUBSET-P (G ':STATES M)
                                                  (G ':STATES M)
                                                  (G ':TRANSITION M))
                             (IF (SUBSET (G ':INITIAL-STATES M)
                                         (G ':STATES M))
                                 (IF (CONSP (G ':STATES M))
                                     (NEXT-STATES-IN-STATES M (G ':STATES M))
                                     'NIL)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 'NIL)
             'NIL)
         'NIL)
     'NIL))

(DEFUN
   C-BISIM-EQUIV (M N VARS)
   (IF (CIRCUIT-MODELP M)
       (IF (CIRCUIT-MODELP N)
           (IF (SUBSET VARS (G ':VARIABLES M))
               (IF (SUBSET VARS (G ':VARIABLES N))
                   (IF (WELL-FORMED-TRANSITION-P (G ':STATES M)
                                                 (G ':TRANSITION M)
                                                 (G ':STATES N)
                                                 (G ':TRANSITION N)
                                                 VARS)
                       (IF (WELL-FORMED-TRANSITION-P (G ':STATES N)
                                                     (G ':TRANSITION N)
                                                     (G ':STATES M)
                                                     (G ':TRANSITION M)
                                                     VARS)
                           (IF (EVALUATION-EQ-SUBSET-P (G ':INITIAL-STATES M)
                                                       (G ':INITIAL-STATES N)
                                                       VARS)
                               (EVALUATION-EQ-SUBSET-P (G ':INITIAL-STATES N)
                                                       (G ':INITIAL-STATES M)
                                                       VARS)
                               'NIL)
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)
           'NIL)
       'NIL))

(DEFUN
 CIRCUIT-BISIM (P M Q N VARS)
 (IF
   (CIRCUIT-MODELP M)
   (IF (CIRCUIT-MODELP N)
       (IF (MEMBERP P (G ':STATES M))
           (IF (MEMBERP Q (G ':STATES N))
               (IF (WELL-FORMED-TRANSITION-P (G ':STATES M)
                                             (G ':TRANSITION M)
                                             (G ':STATES N)
                                             (G ':TRANSITION N)
                                             VARS)
                   (IF (WELL-FORMED-TRANSITION-P (G ':STATES N)
                                                 (G ':TRANSITION N)
                                                 (G ':STATES M)
                                                 (G ':TRANSITION M)
                                                 VARS)
                       (IF (EVALUATION-EQ-SUBSET-P (G ':INITIAL-STATES M)
                                                   (G ':INITIAL-STATES N)
                                                   VARS)
                           (IF (EVALUATION-EQ-SUBSET-P (G ':INITIAL-STATES N)
                                                       (G ':INITIAL-STATES M)
                                                       VARS)
                               (IF (SUBSET VARS (G ':VARIABLES M))
                                   (IF (SUBSET VARS (G ':VARIABLES N))
                                       (EVALUATION-EQ P Q VARS)
                                       'NIL)
                                   'NIL)
                               'NIL)
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)
           'NIL)
       'NIL)
   'NIL))

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

(DEFTHM CONE-OF-INFLUENCE-REDUCTION-IS-CIRCUIT-P
        (IMPLIES (CIRCUITP C)
                 (CIRCUITP (CONE-OF-INFLUENCE-REDUCTION C VARS))))

(DEFTHM
 CONE-OF-INFLUENCE-IS-C-BISIMI-EQUIV
 (IMPLIES (CIRCUITP C)
          (C-BISIM-EQUIV (CREATE-KRIPKE C)
                         (CREATE-KRIPKE (CONE-OF-INFLUENCE-REDUCTION C VARS))
                         (CONE-VARIABLES VARS C))))

(DEFTHM CREATE-KRIPKE-PRODUCES-CIRCUIT-MODEL
        (IMPLIES (CIRCUITP C)
                 (CIRCUIT-MODELP (CREATE-KRIPKE C))))

(DEFUN C-BISIMILAR-INITIAL-STATE-WITNESS-M->N
       (S M N VARS)
       (EVALUATION-EQ-MEMBER S (G ':INITIAL-STATES N)
                             VARS))

(DEFUN C-BISIMILAR-INITIAL-STATE-WITNESS-N->M
       (M S N VARS)
       (EVALUATION-EQ-MEMBER S (G ':INITIAL-STATES M)
                             VARS))

(DEFUN C-BISIMILAR-TRANSITION-WITNESS-M->N
       (P R M Q N VARS)
       (EVALUATION-EQ-MEMBER R (G Q (G ':TRANSITION N))
                             VARS))

(DEFUN C-BISIMILAR-TRANSITION-WITNESS-N->M
       (P M Q R N VARS)
       (EVALUATION-EQ-MEMBER R (G P (G ':TRANSITION M))
                             VARS))

(DEFTHM C-BISIMILAR-EQUIV-IMPLIES-INIT->INIT-M->N
        (IMPLIES (IF (C-BISIM-EQUIV M N VARS)
                     (MEMBERP S (G ':INITIAL-STATES M))
                     'NIL)
                 (MEMBERP (C-BISIMILAR-INITIAL-STATE-WITNESS-M->N S M N VARS)
                          (G ':INITIAL-STATES N))))

(DEFTHM C-BISIMILAR-EQUIV-IMPLIES-INIT->INIT-N->M
        (IMPLIES (IF (C-BISIM-EQUIV M N VARS)
                     (MEMBERP S (G ':INITIAL-STATES N))
                     'NIL)
                 (MEMBERP (C-BISIMILAR-INITIAL-STATE-WITNESS-N->M M S N VARS)
                          (G ':INITIAL-STATES M))))

(DEFTHM
  C-BISIMILAR-EQUIV-IMPLIES-BISIMILAR-INITIAL-STATES-M->N
  (IMPLIES (IF (C-BISIM-EQUIV M N VARS)
               (MEMBERP S (G ':INITIAL-STATES M))
               'NIL)
           (CIRCUIT-BISIM S M
                          (C-BISIMILAR-INITIAL-STATE-WITNESS-M->N S M N VARS)
                          N VARS)))

(DEFTHM
  C-BISIMILAR-EQUIV-IMPLIES-BISIMILAR-INITIAL-STATES-N->M
  (IMPLIES (IF (C-BISIM-EQUIV M N VARS)
               (MEMBERP S (G ':INITIAL-STATES N))
               'NIL)
           (CIRCUIT-BISIM (C-BISIMILAR-INITIAL-STATE-WITNESS-N->M M S N VARS)
                          M S N VARS)))

(DEFTHM C-BISIMILAR-STATES-HAVE-LABELS-EQUAL
        (IMPLIES (CIRCUIT-BISIM P M Q N VARS)
                 (SET-EQUAL (SET-INTERSECT (LABEL-OF Q N) VARS)
                            (SET-INTERSECT (LABEL-OF P M) VARS))))

(DEFTHM
     C-BISIMILAR-WITNESS-MEMBER-OF-STATES-M->N
     (IMPLIES (IF (CIRCUIT-BISIM P M Q N VARS)
                  (IF (NEXT-STATEP P R M)
                      (MEMBERP R (G ':STATES M))
                      'NIL)
                  'NIL)
              (MEMBERP (C-BISIMILAR-TRANSITION-WITNESS-M->N P R M Q N VARS)
                       (G ':STATES N))))

(DEFTHM
     C-BISIMILAR-WITNESS-MEMBER-OF-STATES-N->M
     (IMPLIES (IF (CIRCUIT-BISIM P M Q N VARS)
                  (IF (NEXT-STATEP Q R N)
                      (MEMBERP R (G ':STATES N))
                      'NIL)
                  'NIL)
              (MEMBERP (C-BISIMILAR-TRANSITION-WITNESS-N->M P M Q R N VARS)
                       (G ':STATES M))))

(DEFTHM
 C-BISIMILAR-WITNESS-PRODUCES-BISIMILAR-STATES-M->N
 (IMPLIES (IF (CIRCUIT-BISIM P M Q N VARS)
              (NEXT-STATEP P R M)
              'NIL)
          (CIRCUIT-BISIM R M
                         (C-BISIMILAR-TRANSITION-WITNESS-M->N P R M Q N VARS)
                         N VARS)))

(DEFTHM
 C-BISIMILAR-WITNESS-PRODUCES-BISIMILAR-STATES-N->M
 (IMPLIES (IF (CIRCUIT-BISIM P M Q N VARS)
              (NEXT-STATEP Q R N)
              'NIL)
          (CIRCUIT-BISIM (C-BISIMILAR-TRANSITION-WITNESS-N->M P M Q R N VARS)
                         M R N VARS)))

(DEFTHM
   C-BISIMILAR-WITNESS-MATCHES-TRANSITION-M->N
   (IMPLIES (IF (CIRCUIT-BISIM P M Q N VARS)
                (NEXT-STATEP P R M)
                'NIL)
            (NEXT-STATEP Q
                         (C-BISIMILAR-TRANSITION-WITNESS-M->N P R M Q N VARS)
                         N)))

(DEFTHM
   C-BISIMILAR-WITNESS-MATCHES-TRANSITION-N->M
   (IMPLIES (IF (CIRCUIT-BISIM P M Q N VARS)
                (NEXT-STATEP Q R N)
                'NIL)
            (NEXT-STATEP P
                         (C-BISIMILAR-TRANSITION-WITNESS-N->M P M Q R N VARS)
                         M)))
