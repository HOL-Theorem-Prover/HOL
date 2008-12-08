(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "ltl")

(DEFUN EVALUATION-EQ (P Q VARS)
       (IF (ENDP VARS)
           'T
           (IF (EQUAL (G (CAR VARS) P)
                      (G (CAR VARS) Q))
               (EVALUATION-EQ P Q (CDR VARS))
               'NIL)))

(DEFTHM EVALUATION-EQ-IS-SYMMETRIC
        (EQUAL (EVALUATION-EQ P Q VARS)
               (EVALUATION-EQ Q P VARS)))

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

(DEFTHM MEMBER-IS-MEMBERP
        (IMPLIES (EVALUATION-EQ-MEMBER-P P STATES VARS)
                 (MEMBERP (EVALUATION-EQ-MEMBER P STATES VARS)
                          STATES)))

(DEFTHM MEMBER-IS-EVALUATION-EQ
        (IMPLIES (EVALUATION-EQ-MEMBER-P P STATES VARS)
                 (EVALUATION-EQ P (EVALUATION-EQ-MEMBER P STATES VARS)
                                VARS)))

(DEFUN-SK STRICT-EVALUATION-P (ST VARS)
          (FORALL (V)
                  (IMPLIES (NOT (MEMBERP V VARS))
                           (NOT (G V ST)))))

(DEFTHM STRICT-EVALUATION-P-EXPANDED
        (IMPLIES (IF (STRICT-EVALUATION-P ST VARS)
                     (NOT (MEMBERP V VARS))
                     'NIL)
                 (NOT (G V ST))))

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

(DEFTHM ALL-TRUTHSP-LABEL-EXPANDED
        (IMPLIES (IF (ALL-TRUTHSP-LABEL LABEL S VARS)
                     (IF (MEMBERP V VARS)
                         (EQUAL (G V S) 'T)
                         'NIL)
                     'NIL)
                 (MEMBERP V LABEL)))

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

(DEFTHM LABEL-SUBSET-SUBSET-REDUCTION
        (IMPLIES (IF (LABEL-SUBSET-VARS STATES M VARS)
                     (MEMBERP P STATES)
                     'NIL)
                 (SUBSET (LABEL-OF P M) VARS)))

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

(DEFTHM
   WELL-FORMED-TRANSITION-P-EXPANDED
   (IMPLIES
        (IF (WELL-FORMED-TRANSITION-P STATES-M TRANS-M STATES-N TRANS-N VARS)
            (IF (EVALUATION-EQ P Q VARS)
                (IF (EVALUATION-P P VARS)
                    (IF (MEMBERP P STATES-M)
                        (IF (MEMBERP Q STATES-N)
                            (EVALUATION-P Q VARS)
                            'NIL)
                        'NIL)
                    'NIL)
                'NIL)
            'NIL)
        (EVALUATION-EQ-SUBSET-P (G P TRANS-M)
                                (G Q TRANS-N)
                                VARS)))

(DEFUN TRANSITION-SUBSET-P
       (STATES STATES-PRIME TRANS)
       (IF (ENDP STATES)
           'T
           (IF (SUBSET (G (CAR STATES) TRANS)
                       STATES-PRIME)
               (TRANSITION-SUBSET-P (CDR STATES)
                                    STATES-PRIME TRANS)
               'NIL)))

(DEFTHM TRANSITION-SUBSET-P-EXPANDED
        (IMPLIES (IF (TRANSITION-SUBSET-P STATES STATES-PRIME TRANS)
                     (IF (MEMBERP P STATES)
                         (MEMBERP R (G P TRANS))
                         'NIL)
                     'NIL)
                 (MEMBERP R STATES-PRIME)))

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

(DEFUN C-BISIMILAR-INITIAL-STATE-WITNESS-M->N
       (S M N VARS)
       (EVALUATION-EQ-MEMBER S (G ':INITIAL-STATES N)
                             VARS))

(DEFUN C-BISIMILAR-INITIAL-STATE-WITNESS-N->M
       (M S N VARS)
       (EVALUATION-EQ-MEMBER S (G ':INITIAL-STATES M)
                             VARS))

(DEFTHM ALL-EVALUATIONS-CONSIDERS-AN-EVALUATION-A-MEMBER
        (IMPLIES (IF (EVALUATION-P ST VARS)
                     (ALL-EVALUATIONS-P STATES VARS)
                     'NIL)
                 (EVALUATION-EQ-MEMBER-P ST STATES VARS)))

(DEFTHM TRUTHP-LABEL-FROM-ONLY-TRUTHP
        (IMPLIES (IF (ONLY-TRUTH-P STATES M)
                     (MEMBERP S STATES)
                     'NIL)
                 (TRUTHP-LABEL (LABEL-OF S M) S)))

(DEFTHM ALL-TRUTHS-P-FROM-ONLY-ALL-TRUTHS-P
        (IMPLIES (IF (ONLY-ALL-TRUTHS-P STATES M VARS)
                     (MEMBERP S STATES)
                     'NIL)
                 (ALL-TRUTHSP-LABEL (LABEL-OF S M)
                                    S VARS)))

(DEFTHM MEMBERP-TO-INTERSECT-REDUCTION
        (IMPLIES (MEMBERP V (SET-INTERSECT X Y))
                 (IF (MEMBERP V X) (MEMBERP V Y) 'NIL)))

(DEFTHM EVALUATION-EQ-VARS-REDUCTION
        (IMPLIES (IF (EVALUATION-EQ P Q VARS)
                     (MEMBERP V VARS)
                     'NIL)
                 (EQUAL (G V P) (G V Q))))

(DEFTHM VARIABLES-IN-LABEL-ARE-T-IN-Q
        (IMPLIES (IF (MEMBERP V (SET-INTERSECT LABEL VARS))
                     (IF (TRUTHP-LABEL LABEL P)
                         (EVALUATION-EQ P Q VARS)
                         'NIL)
                     'NIL)
                 (EQUAL (G V Q) 'T)))

(DEFTHM ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET
        (IMPLIES (IF (EQUAL (G V Q) 'T)
                     (IF (MEMBERP V VARS)
                         (IF (SUBSET VARS VARIABLES)
                             (ALL-TRUTHSP-LABEL LABEL Q VARIABLES)
                             'NIL)
                         'NIL)
                     'NIL)
                 (MEMBERP V LABEL)))

(DEFTHM TRUTHP-LABEL-TO-SUBSET
        (IMPLIES (IF (MEMBERP V (SET-INTERSECT LP VARS))
                     (IF (TRUTHP-LABEL LP P)
                         (IF (EVALUATION-EQ P Q VARS)
                             (IF (SUBSET VARS VARIABLES)
                                 (ALL-TRUTHSP-LABEL LQ Q VARIABLES)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 (MEMBERP V LQ)))

(DEFTHM TRUTHP-LABEL-IS-A-SUBSET
        (IMPLIES (IF (TRUTHP-LABEL LP P)
                     (IF (EVALUATION-EQ P Q VARS)
                         (IF (SUBSET VARS VARIABLES)
                             (ALL-TRUTHSP-LABEL LQ Q VARIABLES)
                             'NIL)
                         'NIL)
                     'NIL)
                 (SUBSET (SET-INTERSECT LP VARS) LQ)))

(DEFUN C-BISIMILAR-TRANSITION-WITNESS-M->N
       (P R M Q N VARS)
       (EVALUATION-EQ-MEMBER R (G Q (G ':TRANSITION N))
                             VARS))

(DEFUN C-BISIMILAR-TRANSITION-WITNESS-N->M
       (P M Q R N VARS)
       (EVALUATION-EQ-MEMBER R (G P (G ':TRANSITION M))
                             VARS))

(DEFTHM EVALUATIONP-FOR-SUBSET
        (IMPLIES (IF (EVALUATION-P ST VARIABLES)
                     (SUBSET VARS VARIABLES)
                     'NIL)
                 (EVALUATION-P ST VARS)))

(DEFTHM EVALUATION-P-ONLY-EVALUATIONS-REDUCTION
        (IMPLIES (IF (ONLY-EVALUATIONS-P STATES VARS)
                     (MEMBERP P STATES)
                     'NIL)
                 (EVALUATION-P P VARS)))

(DEFTHM
 R-IS-EVALUATION-EQ-MEMBER-P
 (IMPLIES
    (IF (EVALUATION-EQ P Q VARS)
        (IF (WELL-FORMED-TRANSITION-P STATES-M TRANS-M STATES-N TRANS-N VARS)
            (IF (MEMBERP P STATES-M)
                (IF (MEMBERP Q STATES-N)
                    (IF (EVALUATION-P P VARS)
                        (IF (EVALUATION-P Q VARS)
                            (MEMBERP R (G P TRANS-M))
                            'NIL)
                        'NIL)
                    'NIL)
                'NIL)
            'NIL)
        'NIL)
    (EVALUATION-EQ-MEMBER-P R (G Q TRANS-N)
                            VARS)))

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
