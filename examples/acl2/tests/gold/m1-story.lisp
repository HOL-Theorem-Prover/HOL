(INCLUDE-BOOK "problem-set-1-answers")

; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "M1")

(DEFUN M1::NEXT-INST (M1::S) (M1::NTH (M1::PC M1::S) (M1::PROGRAM M1::S)))

(DEFUN M1::EXECUTE-ICONST (M1::INST M1::S)
       (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                       (M1::LOCALS M1::S)
                       (M1::PUSH (M1::ARG1 M1::INST)
                                 (M1::STACK M1::S))
                       (M1::PROGRAM M1::S)))

(DEFUN M1::EXECUTE-ILOAD (M1::INST M1::S)
       (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                       (M1::LOCALS M1::S)
                       (M1::PUSH (M1::NTH (M1::ARG1 M1::INST)
                                          (M1::LOCALS M1::S))
                                 (M1::STACK M1::S))
                       (M1::PROGRAM M1::S)))

(DEFUN
    M1::EXECUTE-IADD (M1::INST M1::S)
    (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                    (M1::LOCALS M1::S)
                    (M1::PUSH (BINARY-+ (M1::TOP (M1::POP (M1::STACK M1::S)))
                                        (M1::TOP (M1::STACK M1::S)))
                              (M1::POP (M1::POP (M1::STACK M1::S))))
                    (M1::PROGRAM M1::S)))

(DEFUN M1::EXECUTE-ISTORE (M1::INST M1::S)
       (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                       (M1::UPDATE-NTH (M1::ARG1 M1::INST)
                                       (M1::TOP (M1::STACK M1::S))
                                       (M1::LOCALS M1::S))
                       (M1::POP (M1::STACK M1::S))
                       (M1::PROGRAM M1::S)))

(DEFUN
   M1::EXECUTE-ISUB (M1::INST M1::S)
   (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                   (M1::LOCALS M1::S)
                   (M1::PUSH (BINARY-+ (M1::TOP (M1::POP (M1::STACK M1::S)))
                                       (UNARY-- (M1::TOP (M1::STACK M1::S))))
                             (M1::POP (M1::POP (M1::STACK M1::S))))
                   (M1::PROGRAM M1::S)))

(DEFUN
    M1::EXECUTE-IMUL (M1::INST M1::S)
    (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                    (M1::LOCALS M1::S)
                    (M1::PUSH (BINARY-* (M1::TOP (M1::POP (M1::STACK M1::S)))
                                        (M1::TOP (M1::STACK M1::S)))
                              (M1::POP (M1::POP (M1::STACK M1::S))))
                    (M1::PROGRAM M1::S)))

(DEFUN M1::EXECUTE-GOTO (M1::INST M1::S)
       (M1::MAKE-STATE (BINARY-+ (M1::ARG1 M1::INST)
                                 (M1::PC M1::S))
                       (M1::LOCALS M1::S)
                       (M1::STACK M1::S)
                       (M1::PROGRAM M1::S)))

(DEFUN M1::EXECUTE-IFLE (M1::INST M1::S)
       (M1::MAKE-STATE (IF (NOT (< '0 (M1::TOP (M1::STACK M1::S))))
                           (BINARY-+ (M1::ARG1 M1::INST)
                                     (M1::PC M1::S))
                           (BINARY-+ '1 (M1::PC M1::S)))
                       (M1::LOCALS M1::S)
                       (M1::POP (M1::STACK M1::S))
                       (M1::PROGRAM M1::S)))

(DEFUN
     M1::DO-INST (M1::INST M1::S)
     (IF (EQUAL (M1::OP-CODE M1::INST)
                'M1::ICONST)
         (M1::EXECUTE-ICONST M1::INST M1::S)
         (IF (EQUAL (M1::OP-CODE M1::INST)
                    'M1::ILOAD)
             (M1::EXECUTE-ILOAD M1::INST M1::S)
             (IF (EQUAL (M1::OP-CODE M1::INST)
                        'M1::ISTORE)
                 (M1::EXECUTE-ISTORE M1::INST M1::S)
                 (IF (EQUAL (M1::OP-CODE M1::INST) 'M1::IADD)
                     (M1::EXECUTE-IADD M1::INST M1::S)
                     (IF (EQUAL (M1::OP-CODE M1::INST) 'M1::ISUB)
                         (M1::EXECUTE-ISUB M1::INST M1::S)
                         (IF (EQUAL (M1::OP-CODE M1::INST) 'M1::IMUL)
                             (M1::EXECUTE-IMUL M1::INST M1::S)
                             (IF (EQUAL (M1::OP-CODE M1::INST) 'M1::GOTO)
                                 (M1::EXECUTE-GOTO M1::INST M1::S)
                                 (IF (EQUAL (M1::OP-CODE M1::INST) 'M1::IFLE)
                                     (M1::EXECUTE-IFLE M1::INST M1::S)
                                     M1::S)))))))))

(DEFUN M1::STEP (M1::S) (M1::DO-INST (M1::NEXT-INST M1::S) M1::S))

(DEFUN M1::RUN (M1::SCHED M1::S)
       (IF (ENDP M1::SCHED)
           M1::S
           (M1::RUN (CDR M1::SCHED)
                    (M1::STEP M1::S))))

(DEFTHM M1::FACTORIAL-EXAMPLE-0
        (EQUAL (M1::RUN '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (M1::MAKE-STATE '0
                                        '(5 0)
                                        'NIL
                                        '((M1::ICONST 1)
                                          (M1::ISTORE 1)
                                          (M1::ILOAD 0)
                                          (M1::IFLE 10)
                                          (M1::ILOAD 0)
                                          (M1::ILOAD 1)
                                          (M1::IMUL)
                                          (M1::ISTORE 1)
                                          (M1::ILOAD 0)
                                          (M1::ICONST 1)
                                          (M1::ISUB)
                                          (M1::ISTORE 0)
                                          (M1::GOTO -10)
                                          (M1::ILOAD 1)
                                          (M1::HALT))))
               '(14 (0 120)
                    (120)
                    ((M1::ICONST 1)
                     (M1::ISTORE 1)
                     (M1::ILOAD 0)
                     (M1::IFLE 10)
                     (M1::ILOAD 0)
                     (M1::ILOAD 1)
                     (M1::IMUL)
                     (M1::ISTORE 1)
                     (M1::ILOAD 0)
                     (M1::ICONST 1)
                     (M1::ISUB)
                     (M1::ISTORE 0)
                     (M1::GOTO -10)
                     (M1::ILOAD 1)
                     (M1::HALT)))))

(DEFUN M1::IFACT-LOOP-SCHED (M1::N)
       (IF (ZP M1::N)
           (M1::REPEAT '0 '4)
           (M1::APP (M1::REPEAT '0 '11)
                    (M1::IFACT-LOOP-SCHED (BINARY-+ '-1 M1::N)))))

(DEFUN M1::IFACT-SCHED (M1::N)
       (M1::APP (M1::REPEAT '0 '2)
                (M1::IFACT-LOOP-SCHED M1::N)))

(DEFUN M1::! (M1::N)
       (IF (ZP M1::N)
           '1
           (BINARY-* M1::N (M1::! (BINARY-+ '-1 M1::N)))))

(DEFUN
     M1::TEST-IFACT (M1::N)
     (M1::TOP (M1::STACK (M1::RUN (M1::IFACT-SCHED M1::N)
                                  (M1::MAKE-STATE '0
                                                  (CONS M1::N (CONS '0 'NIL))
                                                  'NIL
                                                  '((M1::ICONST 1)
                                                    (M1::ISTORE 1)
                                                    (M1::ILOAD 0)
                                                    (M1::IFLE 10)
                                                    (M1::ILOAD 0)
                                                    (M1::ILOAD 1)
                                                    (M1::IMUL)
                                                    (M1::ISTORE 1)
                                                    (M1::ILOAD 0)
                                                    (M1::ICONST 1)
                                                    (M1::ISUB)
                                                    (M1::ISTORE 0)
                                                    (M1::GOTO -10)
                                                    (M1::ILOAD 1)
                                                    (M1::HALT)))))))

(DEFTHM M1::FACTORIAL-EXAMPLE-1 (EQUAL (M1::TEST-IFACT '5) (M1::! '5)))

(DEFTHM M1::FACTORIAL-EXAMPLE-2
        (EQUAL (M1::TEST-IFACT '1000)
               (M1::! '1000)))

(DEFUN M1::EVEN-SCHED (M1::I)
       (IF (ZP M1::I)
           (M1::REPEAT '0 '4)
           (IF (EQUAL M1::I '1)
               (M1::REPEAT '0 '8)
               (M1::APP (M1::REPEAT '0 '11)
                        (M1::EVEN-SCHED (BINARY-+ '-2 M1::I))))))

(DEFUN M1::TEST-EVEN (M1::I)
       (M1::TOP (M1::STACK (M1::RUN (M1::EVEN-SCHED M1::I)
                                    (M1::MAKE-STATE '0
                                                    (CONS M1::I 'NIL)
                                                    'NIL
                                                    '((M1::ILOAD 0)
                                                      (M1::IFLE 12)
                                                      (M1::ILOAD 0)
                                                      (M1::ICONST 1)
                                                      (M1::ISUB)
                                                      (M1::IFLE 6)
                                                      (M1::ILOAD 0)
                                                      (M1::ICONST 2)
                                                      (M1::ISUB)
                                                      (M1::ISTORE 0)
                                                      (M1::GOTO -10)
                                                      (M1::ICONST 0)
                                                      (M1::HALT)
                                                      (M1::ICONST 1)
                                                      (M1::HALT)))))))

(DEFTHM M1::TEST-EVEN-THEOREM
        (IF (EQUAL (M1::TEST-EVEN '18) '1)
            (IF (EQUAL (M1::TEST-EVEN '19) '0)
                (IF (EQUAL (M1::TEST-EVEN '235) '0)
                    (EQUAL (M1::TEST-EVEN '234) '1)
                    'NIL)
                'NIL)
            'NIL))

(DEFUN M1::COLLECT-AT-END (LIST M1::E)
       (IF (M1::MEMBER M1::E LIST)
           LIST (M1::APP LIST (CONS M1::E 'NIL))))

(DEFTHM M1::NTH-NIL (EQUAL (M1::NTH M1::N 'NIL) 'NIL))

(DEFTHM M1::ACL2-COUNT-NTH
        (IMPLIES (CONSP LIST)
                 (< (ACL2-COUNT (M1::NTH M1::N LIST))
                    (ACL2-COUNT LIST))))

(DEFUN M1::COLLECT-VARS-IN-EXPR
       (M1::VARS M1::EXPR)
       (IF (ATOM M1::EXPR)
           (IF (SYMBOLP M1::EXPR)
               (M1::COLLECT-AT-END M1::VARS M1::EXPR)
               M1::VARS)
           (M1::COLLECT-VARS-IN-EXPR
                (M1::COLLECT-VARS-IN-EXPR M1::VARS (M1::NTH '0 M1::EXPR))
                (M1::NTH '2 M1::EXPR))))

(MUTUAL-RECURSION
  (DEFUN M1::COLLECT-VARS-IN-STMT*
         (M1::VARS M1::STMT-LIST)
         (IF (ENDP M1::STMT-LIST)
             M1::VARS
             (M1::COLLECT-VARS-IN-STMT*
                  (M1::COLLECT-VARS-IN-STMT M1::VARS (CAR M1::STMT-LIST))
                  (CDR M1::STMT-LIST))))
  (DEFUN
       M1::COLLECT-VARS-IN-STMT
       (M1::VARS M1::STMT)
       (IF (EQUAL (M1::NTH '1 M1::STMT) 'M1::=)
           (M1::COLLECT-VARS-IN-EXPR
                (M1::COLLECT-AT-END M1::VARS (M1::NTH '0 M1::STMT))
                (M1::NTH '2 M1::STMT))
           (IF (EQUAL (M1::NTH '0 M1::STMT) 'M1::WHILE)
               (M1::COLLECT-VARS-IN-STMT*
                    (M1::COLLECT-VARS-IN-EXPR M1::VARS (M1::NTH '1 M1::STMT))
                    (CDR (CDR M1::STMT)))
               (IF (EQUAL (M1::NTH '0 M1::STMT)
                          'M1::RETURN)
                   (M1::COLLECT-VARS-IN-EXPR M1::VARS (M1::NTH '1 M1::STMT))
                   M1::VARS)))))

(DEFUN M1::OP! (M1::OP)
       (IF (EQUAL M1::OP '+)
           '((M1::IADD))
           (IF (EQUAL M1::OP '-)
               '((M1::ISUB))
               (IF (EQUAL M1::OP '*)
                   '((M1::IMUL))
                   '((M1::ILLEGAL))))))

(DEFUN M1::ILOAD! (M1::VARS M1::VAR)
       (CONS (CONS 'M1::ILOAD
                   (CONS (M1::INDEX M1::VAR M1::VARS)
                         'NIL))
             'NIL))

(DEFUN M1::ICONST! (M1::N) (CONS (CONS 'M1::ICONST (CONS M1::N 'NIL)) 'NIL))

(DEFUN M1::EXPR! (M1::VARS M1::EXPR)
       (IF (ATOM M1::EXPR)
           (IF (SYMBOLP M1::EXPR)
               (M1::ILOAD! M1::VARS M1::EXPR)
               (M1::ICONST! M1::EXPR))
           (M1::APP (M1::EXPR! M1::VARS (M1::NTH '0 M1::EXPR))
                    (M1::APP (M1::EXPR! M1::VARS (M1::NTH '2 M1::EXPR))
                             (M1::OP! (M1::NTH '1 M1::EXPR))))))

(DEFUN M1::IFLE! (M1::OFFSET)
       (CONS (CONS 'M1::IFLE (CONS M1::OFFSET 'NIL))
             'NIL))

(DEFUN M1::GOTO! (M1::OFFSET)
       (CONS (CONS 'M1::GOTO (CONS M1::OFFSET 'NIL))
             'NIL))

(DEFUN
 M1::WHILE! (M1::TEST-CODE M1::BODY-CODE)
 (M1::APP
  M1::TEST-CODE
  (M1::APP
   (M1::IFLE! (BINARY-+ '2 (M1::LEN M1::BODY-CODE)))
   (M1::APP
      M1::BODY-CODE
      (M1::GOTO! (UNARY-- (BINARY-+ (M1::LEN M1::TEST-CODE)
                                    (BINARY-+ '1
                                              (M1::LEN M1::BODY-CODE)))))))))

(DEFUN M1::TEST! (M1::VARS M1::TEST)
       (IF (EQUAL (M1::NTH '1 M1::TEST) '>)
           (IF (EQUAL (M1::NTH '2 M1::TEST) '0)
               (M1::EXPR! M1::VARS (M1::NTH '0 M1::TEST))
               (M1::APP (M1::EXPR! M1::VARS (M1::NTH '0 M1::TEST))
                        (M1::APP (M1::EXPR! M1::VARS (M1::NTH '2 M1::TEST))
                                 '((M1::ISUB)))))
           '((M1::ILLEGAL))))

(DEFUN M1::ISTORE! (M1::VARS M1::VAR)
       (CONS (CONS 'M1::ISTORE
                   (CONS (M1::INDEX M1::VAR M1::VARS)
                         'NIL))
             'NIL))

(MUTUAL-RECURSION
     (DEFUN M1::STMT*! (M1::VARS M1::STMT-LIST)
            (IF (ENDP M1::STMT-LIST)
                'NIL
                (M1::APP (M1::STMT! M1::VARS (CAR M1::STMT-LIST))
                         (M1::STMT*! M1::VARS (CDR M1::STMT-LIST)))))
     (DEFUN M1::STMT! (M1::VARS M1::STMT)
            (IF (EQUAL (M1::NTH '1 M1::STMT) 'M1::=)
                (M1::APP (M1::EXPR! M1::VARS (M1::NTH '2 M1::STMT))
                         (M1::ISTORE! M1::VARS (M1::NTH '0 M1::STMT)))
                (IF (EQUAL (M1::NTH '0 M1::STMT) 'M1::WHILE)
                    (M1::WHILE! (M1::TEST! M1::VARS (M1::NTH '1 M1::STMT))
                                (M1::STMT*! M1::VARS (CDR (CDR M1::STMT))))
                    (IF (EQUAL (M1::NTH '0 M1::STMT)
                               'M1::RETURN)
                        (M1::APP (M1::EXPR! M1::VARS (M1::NTH '1 M1::STMT))
                                 '((M1::HALT)))
                        '((M1::ILLEGAL)))))))

(DEFUN M1::COMPILE (M1::FORMALS M1::STMT-LIST)
       (M1::STMT*! (M1::COLLECT-VARS-IN-STMT* M1::FORMALS M1::STMT-LIST)
                   M1::STMT-LIST))

(DEFTHM M1::EXAMPLE-COMPILATION-1
        (EQUAL (M1::COMPILE '(M1::N)
                            '((M1::A M1::= 1)
                              (M1::WHILE (M1::N > 0)
                                         (M1::A M1::= (M1::N * M1::A))
                                         (M1::N M1::= (M1::N - 1)))
                              (M1::RETURN M1::A)))
               '((M1::ICONST 1)
                 (M1::ISTORE 1)
                 (M1::ILOAD 0)
                 (M1::IFLE 10)
                 (M1::ILOAD 0)
                 (M1::ILOAD 1)
                 (M1::IMUL)
                 (M1::ISTORE 1)
                 (M1::ILOAD 0)
                 (M1::ICONST 1)
                 (M1::ISUB)
                 (M1::ISTORE 0)
                 (M1::GOTO -10)
                 (M1::ILOAD 1)
                 (M1::HALT))))

(DEFTHM M1::EXAMPLE-COMPILATION-2
        (EQUAL (M1::COMPILE '(M1::N M1::K)
                            '((M1::A M1::= 0)
                              (M1::WHILE (M1::N > M1::K)
                                         (M1::A M1::= (M1::A + 1))
                                         (M1::N M1::= (M1::N - 1)))
                              (M1::RETURN M1::A)))
               '((M1::ICONST 0)
                 (M1::ISTORE 2)
                 (M1::ILOAD 0)
                 (M1::ILOAD 1)
                 (M1::ISUB)
                 (M1::IFLE 10)
                 (M1::ILOAD 2)
                 (M1::ICONST 1)
                 (M1::IADD)
                 (M1::ISTORE 2)
                 (M1::ILOAD 0)
                 (M1::ICONST 1)
                 (M1::ISUB)
                 (M1::ISTORE 0)
                 (M1::GOTO -12)
                 (M1::ILOAD 2)
                 (M1::HALT))))

(DEFTHM
 M1::EXAMPLE-EXECUTION-1
 (EQUAL
  (M1::TOP
   (M1::STACK
    (M1::RUN
      (M1::REPEAT '0 '1000)
      (M1::MAKE-STATE '0
                      '(5 0)
                      'NIL
                      (M1::COMPILE '(M1::N)
                                   '((M1::A M1::= 1)
                                     (M1::WHILE (M1::N > 0)
                                                (M1::A M1::= (M1::N * M1::A))
                                                (M1::N M1::= (M1::N - 1)))
                                     (M1::RETURN M1::A)))))))
  '120))

(DEFTHM
 M1::EXAMPLE-EXECUTION-2
 (EQUAL
  (M1::TOP
   (M1::STACK
    (M1::RUN
         (M1::REPEAT '0 '1000)
         (M1::MAKE-STATE '0
                         '(10 4 0)
                         'NIL
                         (M1::COMPILE '(M1::N M1::K)
                                      '((M1::A M1::= 0)
                                        (M1::WHILE (M1::N > M1::K)
                                                   (M1::A M1::= (M1::A + 1))
                                                   (M1::N M1::= (M1::N - 1)))
                                        (M1::RETURN M1::A)))))))
  '6))

(INCLUDE-BOOK "arithmetic-3/extra/top-ext" :DIR :SYSTEM)

(DEFTHM M1::STACKS
        (IF (EQUAL (M1::TOP (M1::PUSH M1::X M1::S))
                   M1::X)
            (IF (EQUAL (M1::POP (M1::PUSH M1::X M1::S))
                       M1::S)
                (IF (EQUAL (M1::TOP (CONS M1::X M1::S))
                           M1::X)
                    (EQUAL (M1::POP (CONS M1::X M1::S))
                           M1::S)
                    'NIL)
                'NIL)
            'NIL))

(DEFTHM
 M1::STATES
 (IF
  (EQUAL (M1::PC (M1::MAKE-STATE M1::PC
                                 M1::LOCALS M1::STACK M1::PROGRAM))
         M1::PC)
  (IF
   (EQUAL (M1::LOCALS (M1::MAKE-STATE M1::PC
                                      M1::LOCALS M1::STACK M1::PROGRAM))
          M1::LOCALS)
   (IF
    (EQUAL (M1::STACK (M1::MAKE-STATE M1::PC
                                      M1::LOCALS M1::STACK M1::PROGRAM))
           M1::STACK)
    (IF
     (EQUAL (M1::PROGRAM (M1::MAKE-STATE M1::PC
                                         M1::LOCALS M1::STACK M1::PROGRAM))
            M1::PROGRAM)
     (IF
      (EQUAL (M1::PC (CONS M1::PC M1::X))
             M1::PC)
      (IF
       (EQUAL (M1::LOCALS (CONS M1::PC (CONS M1::LOCALS M1::X)))
              M1::LOCALS)
       (IF
         (EQUAL (M1::STACK (CONS M1::PC
                                 (CONS M1::LOCALS (CONS M1::STACK M1::X))))
                M1::STACK)
         (EQUAL (M1::PROGRAM
                     (CONS M1::PC
                           (CONS M1::LOCALS
                                 (CONS M1::STACK (CONS M1::PROGRAM M1::X)))))
                M1::PROGRAM)
         'NIL)
       'NIL)
      'NIL)
     'NIL)
    'NIL)
   'NIL)
  'NIL))

(DEFTHM M1::STEP-OPENER
        (IMPLIES (CONSP (M1::NEXT-INST M1::S))
                 (EQUAL (M1::STEP M1::S)
                        (M1::DO-INST (M1::NEXT-INST M1::S)
                                     M1::S))))

(DEFTHM M1::RUN-APP
        (EQUAL (M1::RUN (M1::APP M1::A M1::B) M1::S)
               (M1::RUN M1::B (M1::RUN M1::A M1::S))))

(DEFTHM M1::RUN-OPENER
        (IF (EQUAL (M1::RUN 'NIL M1::S) M1::S)
            (EQUAL (M1::RUN (CONS M1::TH M1::SCHED) M1::S)
                   (M1::RUN M1::SCHED (M1::STEP M1::S)))
            'NIL))

(DEFTHM M1::NTH-ADD1!
        (IMPLIES (NATP M1::N)
                 (EQUAL (M1::NTH (BINARY-+ '1 M1::N) LIST)
                        (M1::NTH M1::N (CDR LIST)))))

(DEFTHM M1::NTH-UPDATE-NTH
        (IMPLIES (IF (NATP M1::I) (NATP M1::J) 'NIL)
                 (EQUAL (M1::NTH M1::I (M1::UPDATE-NTH M1::J M1::V LIST))
                        (IF (EQUAL M1::I M1::J)
                            M1::V (M1::NTH M1::I LIST)))))

(DEFTHM
     M1::UPDATE-NTH-UPDATE-NTH-1
     (IMPLIES (IF (NATP M1::I)
                  (IF (NATP M1::J)
                      (NOT (EQUAL M1::I M1::J))
                      'NIL)
                  'NIL)
              (EQUAL (M1::UPDATE-NTH M1::I
                                     M1::V (M1::UPDATE-NTH M1::J M1::W LIST))
                     (M1::UPDATE-NTH M1::J M1::W
                                     (M1::UPDATE-NTH M1::I M1::V LIST)))))

(DEFTHM M1::UPDATE-NTH-UPDATE-NTH-2
        (EQUAL (M1::UPDATE-NTH M1::I
                               M1::V (M1::UPDATE-NTH M1::I M1::W LIST))
               (M1::UPDATE-NTH M1::I M1::V LIST)))

(DEFUN M1::! (M1::N)
       (IF (ZP M1::N)
           '1
           (BINARY-* M1::N (M1::! (BINARY-+ '-1 M1::N)))))

(DEFUN M1::IFACT (M1::N M1::A)
       (IF (ZP M1::N)
           M1::A
           (M1::IFACT (BINARY-+ '-1 M1::N)
                      (BINARY-* M1::N M1::A))))

(DEFUN M1::IFACT-LOOP-SCHED (M1::N)
       (IF (ZP M1::N)
           (M1::REPEAT '0 '4)
           (M1::APP (M1::REPEAT '0 '11)
                    (M1::IFACT-LOOP-SCHED (BINARY-+ '-1 M1::N)))))

(DEFUN M1::IFACT-SCHED (M1::N)
       (M1::APP (M1::REPEAT '0 '2)
                (M1::IFACT-LOOP-SCHED M1::N)))

(DEFUN
     M1::TEST-IFACT (M1::N)
     (M1::TOP (M1::STACK (M1::RUN (M1::IFACT-SCHED M1::N)
                                  (M1::MAKE-STATE '0
                                                  (CONS M1::N (CONS '0 'NIL))
                                                  'NIL
                                                  '((M1::ICONST 1)
                                                    (M1::ISTORE 1)
                                                    (M1::ILOAD 0)
                                                    (M1::IFLE 10)
                                                    (M1::ILOAD 0)
                                                    (M1::ILOAD 1)
                                                    (M1::IMUL)
                                                    (M1::ISTORE 1)
                                                    (M1::ILOAD 0)
                                                    (M1::ICONST 1)
                                                    (M1::ISUB)
                                                    (M1::ISTORE 0)
                                                    (M1::GOTO -10)
                                                    (M1::ILOAD 1)
                                                    (M1::HALT)))))))

(DEFTHM M1::TEST-IFACT-EXAMPLES
        (IF (EQUAL (M1::TEST-IFACT '5) (M1::! '5))
            (IF (EQUAL (M1::TEST-IFACT '10) (M1::! '10))
                (EQUAL (M1::TEST-IFACT '100)
                       (M1::! '100))
                'NIL)
            'NIL))

(DEFTHM
   M1::IFACT-LOOP-LEMMA
   (IMPLIES (IF (NATP M1::N) (NATP M1::A) 'NIL)
            (EQUAL (M1::RUN (M1::IFACT-LOOP-SCHED M1::N)
                            (M1::MAKE-STATE '2
                                            (CONS M1::N (CONS M1::A 'NIL))
                                            M1::STACK
                                            '((M1::ICONST 1)
                                              (M1::ISTORE 1)
                                              (M1::ILOAD 0)
                                              (M1::IFLE 10)
                                              (M1::ILOAD 0)
                                              (M1::ILOAD 1)
                                              (M1::IMUL)
                                              (M1::ISTORE 1)
                                              (M1::ILOAD 0)
                                              (M1::ICONST 1)
                                              (M1::ISUB)
                                              (M1::ISTORE 0)
                                              (M1::GOTO -10)
                                              (M1::ILOAD 1)
                                              (M1::HALT))))
                   (M1::MAKE-STATE '14
                                   (CONS '0
                                         (CONS (M1::IFACT M1::N M1::A) 'NIL))
                                   (M1::PUSH (M1::IFACT M1::N M1::A)
                                             M1::STACK)
                                   '((M1::ICONST 1)
                                     (M1::ISTORE 1)
                                     (M1::ILOAD 0)
                                     (M1::IFLE 10)
                                     (M1::ILOAD 0)
                                     (M1::ILOAD 1)
                                     (M1::IMUL)
                                     (M1::ISTORE 1)
                                     (M1::ILOAD 0)
                                     (M1::ICONST 1)
                                     (M1::ISUB)
                                     (M1::ISTORE 0)
                                     (M1::GOTO -10)
                                     (M1::ILOAD 1)
                                     (M1::HALT))))))

(DEFTHM
     M1::IFACT-LEMMA
     (IMPLIES (NATP M1::N)
              (EQUAL (M1::RUN (M1::IFACT-SCHED M1::N)
                              (M1::MAKE-STATE '0
                                              (CONS M1::N (CONS M1::A 'NIL))
                                              M1::STACK
                                              '((M1::ICONST 1)
                                                (M1::ISTORE 1)
                                                (M1::ILOAD 0)
                                                (M1::IFLE 10)
                                                (M1::ILOAD 0)
                                                (M1::ILOAD 1)
                                                (M1::IMUL)
                                                (M1::ISTORE 1)
                                                (M1::ILOAD 0)
                                                (M1::ICONST 1)
                                                (M1::ISUB)
                                                (M1::ISTORE 0)
                                                (M1::GOTO -10)
                                                (M1::ILOAD 1)
                                                (M1::HALT))))
                     (M1::MAKE-STATE '14
                                     (CONS '0
                                           (CONS (M1::IFACT M1::N '1) 'NIL))
                                     (M1::PUSH (M1::IFACT M1::N '1)
                                               M1::STACK)
                                     '((M1::ICONST 1)
                                       (M1::ISTORE 1)
                                       (M1::ILOAD 0)
                                       (M1::IFLE 10)
                                       (M1::ILOAD 0)
                                       (M1::ILOAD 1)
                                       (M1::IMUL)
                                       (M1::ISTORE 1)
                                       (M1::ILOAD 0)
                                       (M1::ICONST 1)
                                       (M1::ISUB)
                                       (M1::ISTORE 0)
                                       (M1::GOTO -10)
                                       (M1::ILOAD 1)
                                       (M1::HALT))))))

(DEFTHM M1::IFACT-IS-FACTORIAL
        (IMPLIES (IF (NATP M1::N) (NATP M1::A) 'NIL)
                 (EQUAL (M1::IFACT M1::N M1::A)
                        (BINARY-* (M1::! M1::N) M1::A))))

(DEFTHM
     M1::IFACT-CORRECT
     (IMPLIES (NATP M1::N)
              (EQUAL (M1::RUN (M1::IFACT-SCHED M1::N)
                              (M1::MAKE-STATE '0
                                              (CONS M1::N (CONS M1::A 'NIL))
                                              M1::STACK
                                              '((M1::ICONST 1)
                                                (M1::ISTORE 1)
                                                (M1::ILOAD 0)
                                                (M1::IFLE 10)
                                                (M1::ILOAD 0)
                                                (M1::ILOAD 1)
                                                (M1::IMUL)
                                                (M1::ISTORE 1)
                                                (M1::ILOAD 0)
                                                (M1::ICONST 1)
                                                (M1::ISUB)
                                                (M1::ISTORE 0)
                                                (M1::GOTO -10)
                                                (M1::ILOAD 1)
                                                (M1::HALT))))
                     (M1::MAKE-STATE '14
                                     (CONS '0 (CONS (M1::! M1::N) 'NIL))
                                     (M1::PUSH (M1::! M1::N) M1::STACK)
                                     '((M1::ICONST 1)
                                       (M1::ISTORE 1)
                                       (M1::ILOAD 0)
                                       (M1::IFLE 10)
                                       (M1::ILOAD 0)
                                       (M1::ILOAD 1)
                                       (M1::IMUL)
                                       (M1::ISTORE 1)
                                       (M1::ILOAD 0)
                                       (M1::ICONST 1)
                                       (M1::ISUB)
                                       (M1::ISTORE 0)
                                       (M1::GOTO -10)
                                       (M1::ILOAD 1)
                                       (M1::HALT))))))

(DEFTHM
 M1::IFACT-CORRECT-COROLLARY-1
 (IMPLIES
  (NATP M1::N)
  (EQUAL
      (M1::TOP
           (M1::STACK (M1::RUN (M1::IFACT-SCHED M1::N)
                               (M1::MAKE-STATE '0
                                               (CONS M1::N (CONS M1::A 'NIL))
                                               M1::STACK
                                               '((M1::ICONST 1)
                                                 (M1::ISTORE 1)
                                                 (M1::ILOAD 0)
                                                 (M1::IFLE 10)
                                                 (M1::ILOAD 0)
                                                 (M1::ILOAD 1)
                                                 (M1::IMUL)
                                                 (M1::ISTORE 1)
                                                 (M1::ILOAD 0)
                                                 (M1::ICONST 1)
                                                 (M1::ISUB)
                                                 (M1::ISTORE 0)
                                                 (M1::GOTO -10)
                                                 (M1::ILOAD 1)
                                                 (M1::HALT))))))
      (M1::! M1::N))))

(DEFTHM
 M1::IFACT-CORRECT-COROLLARY-2
 (IMPLIES
  (NATP M1::N)
  (EQUAL
   (M1::TOP
    (M1::STACK
     (M1::RUN
      (M1::IFACT-SCHED M1::N)
      (M1::MAKE-STATE '0
                      (CONS M1::N (CONS M1::A 'NIL))
                      M1::STACK
                      (M1::COMPILE '(M1::N)
                                   '((M1::A M1::= 1)
                                     (M1::WHILE (M1::N > 0)
                                                (M1::A M1::= (M1::N * M1::A))
                                                (M1::N M1::= (M1::N - 1)))
                                     (M1::RETURN M1::A)))))))
   (M1::! M1::N))))

(DEFTHM M1::EXAMPLE-MODIFY-1
        (EQUAL (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                               (M1::LOCALS M1::S)
                               (M1::PUSH (M1::ARG1 M1::INST)
                                         (M1::STACK M1::S))
                               (M1::PROGRAM M1::S))
               (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                               (M1::LOCALS M1::S)
                               (M1::PUSH (M1::ARG1 M1::INST)
                                         (M1::STACK M1::S))
                               (M1::PROGRAM M1::S))))

(DEFTHM M1::EXAMPLE-MODIFY-2
        (EQUAL (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                               (M1::UPDATE-NTH (M1::ARG1 M1::INST)
                                               (M1::TOP (M1::STACK M1::S))
                                               (M1::LOCALS M1::S))
                               (M1::POP (M1::STACK M1::S))
                               (M1::PROGRAM M1::S))
               (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                               (M1::UPDATE-NTH (M1::ARG1 M1::INST)
                                               (M1::TOP (M1::STACK M1::S))
                                               (M1::LOCALS M1::S))
                               (M1::POP (M1::STACK M1::S))
                               (M1::PROGRAM M1::S))))

(DEFTHM M1::EXAMPLE-MODIFY-3
        (EQUAL (M1::MAKE-STATE (BINARY-+ (M1::ARG1 M1::INST)
                                         (M1::PC M1::S))
                               (M1::LOCALS M1::S)
                               (M1::STACK M1::S)
                               (M1::PROGRAM M1::S))
               (M1::MAKE-STATE (BINARY-+ (M1::ARG1 M1::INST)
                                         (M1::PC M1::S))
                               (M1::LOCALS M1::S)
                               (M1::STACK M1::S)
                               (M1::PROGRAM M1::S))))

(DEFUN M1::PATTERN-BINDINGS
       (M1::VARS M1::ARG-EXPRESSIONS)
       (IF (ENDP M1::VARS)
           'NIL
           (CONS (CONS (CAR M1::VARS)
                       (CONS (CAR M1::ARG-EXPRESSIONS) 'NIL))
                 (M1::PATTERN-BINDINGS (CDR M1::VARS)
                                       (CDR M1::ARG-EXPRESSIONS)))))

(DEFTHM M1::EXAMPLE-SEMANTICS-1
        (EQUAL ((LAMBDA (M1::C M1::-PC- M1::-LOCALS-
                               M1::-STACK- M1::-PROGRAM- M1::S)
                        (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                                        (M1::LOCALS M1::S)
                                        (M1::PUSH M1::C M1::-STACK-)
                                        (M1::PROGRAM M1::S)))
                (M1::ARG1 M1::INST)
                (M1::PC M1::S)
                (M1::LOCALS M1::S)
                (M1::STACK M1::S)
                (M1::PROGRAM M1::S)
                M1::S)
               (M1::MAKE-STATE (BINARY-+ '1 (M1::PC M1::S))
                               (M1::LOCALS M1::S)
                               (M1::PUSH (M1::ARG1 M1::INST)
                                         (M1::STACK M1::S))
                               (M1::PROGRAM M1::S))))

(DEFUN M1::CONCAT-SYMBOLS (M1::PART1 M1::PART2)
       (INTERN-IN-PACKAGE-OF-SYMBOL
            (COERCE (M1::APP (COERCE (SYMBOL-NAME M1::PART1) 'LIST)
                             (COERCE (SYMBOL-NAME M1::PART2) 'LIST))
                    'STRING)
            'M1::RUN))

(DEFUN M1::MAKE-DEFUN
       (M1::NAME M1::ARGS M1::DCL M1::BODY)
       (IF M1::DCL
           (CONS 'DEFUN
                 (CONS M1::NAME
                       (CONS M1::ARGS
                             (CONS M1::DCL (CONS M1::BODY 'NIL)))))
           (CONS 'DEFUN
                 (CONS M1::NAME
                       (CONS M1::ARGS (CONS M1::BODY 'NIL))))))
