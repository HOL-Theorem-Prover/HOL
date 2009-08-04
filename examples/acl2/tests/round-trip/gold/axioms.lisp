(IN-PACKAGE "ACL2")

(DEFUN IFF (P Q) (IF P (IF Q 'T 'NIL) (IF Q 'NIL 'T)))

(DEFUN XOR (P Q) (IF P (IF Q 'NIL 'T) (IF Q 'T 'NIL)))

(DEFUN BOOLEANP (X) (IF (EQUAL X 'T) 'T (EQUAL X 'NIL)))

(DEFTHM IFF-IS-AN-EQUIVALENCE
        (IF (BOOLEANP (IFF X Y))
            (IF (IFF X X)
                (IF (IMPLIES (IFF X Y) (IFF Y X))
                    (IMPLIES (IF (IFF X Y) (IFF Y Z) 'NIL)
                             (IFF X Z))
                    'NIL)
                'NIL)
            'NIL))

(DEFUN IMPLIES (P Q) (IF P (IF Q 'T 'NIL) 'T))

(DEFTHM IFF-IMPLIES-EQUAL-IMPLIES-1
        (IMPLIES (IFF Y Y-EQUIV)
                 (EQUAL (IMPLIES X Y)
                        (IMPLIES X Y-EQUIV))))

(DEFTHM IFF-IMPLIES-EQUAL-IMPLIES-2
        (IMPLIES (IFF X X-EQUIV)
                 (EQUAL (IMPLIES X Y)
                        (IMPLIES X-EQUIV Y))))

(DEFUN NOT (P) (IF P 'NIL 'T))

(DEFTHM IFF-IMPLIES-EQUAL-NOT
        (IMPLIES (IFF X X-EQUIV)
                 (EQUAL (NOT X) (NOT X-EQUIV))))

(DEFUN HIDE (X) X)

(DEFUN REWRITE-EQUIV (X) X)

(DEFUN EQ (X Y) (EQUAL X Y))

(DEFUN TRUE-LISTP (X) (IF (CONSP X) (TRUE-LISTP (CDR X)) (EQ X 'NIL)))

(DEFUN LIST-MACRO (LST)
       (IF (CONSP LST)
           (CONS 'CONS
                 (CONS (CAR LST)
                       (CONS (LIST-MACRO (CDR LST)) 'NIL)))
           'NIL))

(DEFUN AND-MACRO (LST)
       (IF (CONSP LST)
           (IF (CONSP (CDR LST))
               (CONS 'IF
                     (CONS (CAR LST)
                           (CONS (AND-MACRO (CDR LST))
                                 (CONS 'NIL 'NIL))))
               (CAR LST))
           'T))

(DEFUN OR-MACRO (LST)
       (IF (CONSP LST)
           (IF (CONSP (CDR LST))
               (CONS 'IF
                     (CONS (CAR LST)
                           (CONS (CAR LST)
                                 (CONS (OR-MACRO (CDR LST)) 'NIL))))
               (CAR LST))
           'NIL))

(DEFTHM BOOLEANP-COMPOUND-RECOGNIZER
        (EQUAL (BOOLEANP X)
               (IF (EQUAL X 'T)
                   (EQUAL X 'T)
                   (EQUAL X 'NIL))))

(DEFUN INTEGER-ABS (X) (IF (INTEGERP X) (IF (< X '0) (UNARY-- X) X) '0))

(DEFUN XXXJOIN (FN ARGS)
       (IF (CDR (CDR ARGS))
           (CONS FN
                 (CONS (CAR ARGS)
                       (CONS (XXXJOIN FN (CDR ARGS)) 'NIL)))
           (CONS FN ARGS)))

(DEFUN LEN (X) (IF (CONSP X) (BINARY-+ '1 (LEN (CDR X))) '0))

(DEFUN LENGTH (X) (IF (STRINGP X) (LEN (COERCE X 'LIST)) (LEN X)))

(DEFUN ACL2-COUNT (X)
       (IF (CONSP X)
           (BINARY-+ '1
                     (BINARY-+ (ACL2-COUNT (CAR X))
                               (ACL2-COUNT (CDR X))))
           (IF (RATIONALP X)
               (IF (INTEGERP X)
                   (INTEGER-ABS X)
                   (BINARY-+ (INTEGER-ABS (NUMERATOR X))
                             (DENOMINATOR X)))
               (IF (COMPLEX-RATIONALP X)
                   (BINARY-+ '1
                             (BINARY-+ (ACL2-COUNT (REALPART X))
                                       (ACL2-COUNT (IMAGPART X))))
                   (IF (STRINGP X) (LENGTH X) '0)))))

(DEFUN COND-CLAUSESP (CLAUSES)
       (IF (CONSP CLAUSES)
           (IF (CONSP (CAR CLAUSES))
               (IF (TRUE-LISTP (CAR CLAUSES))
                   (IF (< (LEN (CAR CLAUSES)) '3)
                       (COND-CLAUSESP (CDR CLAUSES))
                       'NIL)
                   'NIL)
               'NIL)
           (EQ CLAUSES 'NIL)))

(DEFUN COND-MACRO (CLAUSES)
       (IF (CONSP CLAUSES)
           (IF (IF (EQ (CAR (CAR CLAUSES)) 'T)
                   (EQ (CDR CLAUSES) 'NIL)
                   'NIL)
               (IF (CDR (CAR CLAUSES))
                   (CAR (CDR (CAR CLAUSES)))
                   (CAR (CAR CLAUSES)))
               (IF (CDR (CAR CLAUSES))
                   (CONS 'IF
                         (CONS (CAR (CAR CLAUSES))
                               (CONS (CAR (CDR (CAR CLAUSES)))
                                     (CONS (COND-MACRO (CDR CLAUSES))
                                           'NIL))))
                   (CONS 'OR
                         (CONS (CAR (CAR CLAUSES))
                               (CONS (COND-MACRO (CDR CLAUSES))
                                     'NIL)))))
           'NIL))

(DEFUN EQLABLEP (X)
       (IF (ACL2-NUMBERP X)
           (ACL2-NUMBERP X)
           (IF (SYMBOLP X)
               (SYMBOLP X)
               (CHARACTERP X))))

(DEFTHM EQLABLEP-RECOG
        (EQUAL (EQLABLEP X)
               (IF (ACL2-NUMBERP X)
                   (ACL2-NUMBERP X)
                   (IF (SYMBOLP X)
                       (SYMBOLP X)
                       (CHARACTERP X)))))

(DEFUN EQLABLE-LISTP (L)
       (IF (CONSP L)
           (IF (EQLABLEP (CAR L))
               (EQLABLE-LISTP (CDR L))
               'NIL)
           (EQUAL L 'NIL)))

(DEFUN ATOM (X) (NOT (CONSP X)))

(DEFUN MAKE-CHARACTER-LIST (X)
       (IF (ATOM X)
           'NIL
           (IF (CHARACTERP (CAR X))
               (CONS (CAR X)
                     (MAKE-CHARACTER-LIST (CDR X)))
               (CONS (CODE-CHAR '0)
                     (MAKE-CHARACTER-LIST (CDR X))))))

(DEFUN EQLABLE-ALISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (CONSP (CAR X))
               (IF (EQLABLEP (CAR (CAR X)))
                   (EQLABLE-ALISTP (CDR X))
                   'NIL)
               'NIL)))

(DEFUN ALISTP (L)
       (IF (ATOM L)
           (EQ L 'NIL)
           (IF (CONSP (CAR L))
               (ALISTP (CDR L))
               'NIL)))

(DEFTHM ALISTP-FORWARD-TO-TRUE-LISTP (IMPLIES (ALISTP X) (TRUE-LISTP X)))

(DEFTHM EQLABLE-ALISTP-FORWARD-TO-ALISTP
        (IMPLIES (EQLABLE-ALISTP X) (ALISTP X)))

(DEFUN ACONS (KEY DATUM ALIST) (CONS (CONS KEY DATUM) ALIST))

(DEFUN ENDP (X) (ATOM X))

(DEFUN MUST-BE-EQUAL (LOGIC EXEC) LOGIC)

(DEFUN MEMBER-EQUAL (X LST)
       (IF (ENDP LST)
           'NIL
           (IF (EQUAL X (CAR LST))
               LST (MEMBER-EQUAL X (CDR LST)))))

(DEFUN UNION-EQUAL (X Y)
       (IF (ENDP X)
           Y
           (IF (MEMBER-EQUAL (CAR X) Y)
               (UNION-EQUAL (CDR X) Y)
               (CONS (CAR X)
                     (UNION-EQUAL (CDR X) Y)))))

(DEFUN SUBSETP-EQUAL (X Y)
       (IF (ENDP X)
           'T
           (IF (MEMBER-EQUAL (CAR X) Y)
               (SUBSETP-EQUAL (CDR X) Y)
               'NIL)))

(DEFUN SYMBOL-LISTP (LST)
       (IF (ATOM LST)
           (EQ LST 'NIL)
           (IF (SYMBOLP (CAR LST))
               (SYMBOL-LISTP (CDR LST))
               'NIL)))

(DEFTHM SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP
        (IMPLIES (SYMBOL-LISTP X)
                 (TRUE-LISTP X)))

(DEFUN NULL (X) (EQ X 'NIL))

(DEFUN MEMBER-EQ (X LST)
       (IF (ENDP LST)
           'NIL
           (IF (EQ X (CAR LST))
               LST (MEMBER-EQ X (CDR LST)))))

(DEFUN SUBSETP-EQ (X Y)
       (IF (ENDP X)
           'T
           (IF (MEMBER-EQ (CAR X) Y)
               (SUBSETP-EQ (CDR X) Y)
               'NIL)))

(DEFUN SYMBOL-ALISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (CONSP (CAR X))
               (IF (SYMBOLP (CAR (CAR X)))
                   (SYMBOL-ALISTP (CDR X))
                   'NIL)
               'NIL)))

(DEFTHM SYMBOL-ALISTP-FORWARD-TO-EQLABLE-ALISTP
        (IMPLIES (SYMBOL-ALISTP X)
                 (EQLABLE-ALISTP X)))

(DEFUN ASSOC-EQ (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQ X (CAR (CAR ALIST)))
               (CAR ALIST)
               (ASSOC-EQ X (CDR ALIST)))))

(DEFUN ASSOC-EQUAL (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQUAL X (CAR (CAR ALIST)))
               (CAR ALIST)
               (ASSOC-EQUAL X (CDR ALIST)))))

(DEFUN ASSOC-EQ-EQUAL-ALISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (CONSP (CAR X))
               (IF (SYMBOLP (CAR (CAR X)))
                   (IF (CONSP (CDR (CAR X)))
                       (ASSOC-EQ-EQUAL-ALISTP (CDR X))
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN ASSOC-EQ-EQUAL (X Y ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (IF (EQ (CAR (CAR ALIST)) X)
                   (EQUAL (CAR (CDR (CAR ALIST))) Y)
                   'NIL)
               (CAR ALIST)
               (ASSOC-EQ-EQUAL X Y (CDR ALIST)))))

(DEFUN NO-DUPLICATESP-EQUAL (L)
       (IF (ENDP L)
           'T
           (IF (MEMBER-EQUAL (CAR L) (CDR L))
               'NIL
               (NO-DUPLICATESP-EQUAL (CDR L)))))

(DEFUN STRIP-CARS (X)
       (IF (ENDP X)
           'NIL
           (CONS (CAR (CAR X))
                 (STRIP-CARS (CDR X)))))

(DEFUN EQL (X Y) (EQUAL X Y))

(DEFUN = (X Y) (EQUAL X Y))

(DEFUN /= (X Y) (NOT (EQUAL X Y)))

(DEFUN ZP (X) (IF (INTEGERP X) (NOT (< '0 X)) 'T))

(DEFTHM ZP-COMPOUND-RECOGNIZER
        (EQUAL (ZP X)
               (IF (NOT (INTEGERP X))
                   (NOT (INTEGERP X))
                   (NOT (< '0 X)))))

(DEFTHM ZP-OPEN
        (IMPLIES (SYNP 'NIL
                       '(SYNTAXP (NOT (VARIABLEP X)))
                       '(IF (NOT (ATOM X)) 'T 'NIL))
                 (EQUAL (ZP X)
                        (IF (INTEGERP X) (NOT (< '0 X)) 'T))))

(DEFUN ZIP (X) (IF (INTEGERP X) (= X '0) 'T))

(DEFTHM ZIP-COMPOUND-RECOGNIZER
        (EQUAL (ZIP X)
               (IF (NOT (INTEGERP X))
                   (NOT (INTEGERP X))
                   (EQUAL X '0))))

(DEFTHM ZIP-OPEN
        (IMPLIES (SYNP 'NIL
                       '(SYNTAXP (NOT (VARIABLEP X)))
                       '(IF (NOT (ATOM X)) 'T 'NIL))
                 (EQUAL (ZIP X)
                        (IF (NOT (INTEGERP X))
                            (NOT (INTEGERP X))
                            (EQUAL X '0)))))

(DEFUN NTH (N L)
       (IF (ENDP L)
           'NIL
           (IF (ZP N)
               (CAR L)
               (NTH (BINARY-+ '-1 N) (CDR L)))))

(DEFUN CHAR (S N) (NTH N (COERCE S 'LIST)))

(DEFUN PROPER-CONSP (X) (IF (CONSP X) (TRUE-LISTP X) 'NIL))

(DEFUN IMPROPER-CONSP (X) (IF (CONSP X) (NOT (TRUE-LISTP X)) 'NIL))

(DEFUN CONJUGATE (X)
       (IF (COMPLEX-RATIONALP X)
           (COMPLEX (REALPART X)
                    (UNARY-- (IMAGPART X)))
           X))

(DEFUN PROG2$ (X Y) Y)

(DEFUN TIME$ (X) X)

(DEFUN EC-CALL (X) X)

(DEFAXIOM CLOSURE
          (IF (ACL2-NUMBERP (BINARY-+ X Y))
              (IF (ACL2-NUMBERP (BINARY-* X Y))
                  (IF (ACL2-NUMBERP (UNARY-- X))
                      (ACL2-NUMBERP (UNARY-/ X))
                      'NIL)
                  'NIL)
              'NIL))

(DEFAXIOM ASSOCIATIVITY-OF-+
          (EQUAL (BINARY-+ (BINARY-+ X Y) Z)
                 (BINARY-+ X (BINARY-+ Y Z))))

(DEFAXIOM COMMUTATIVITY-OF-+ (EQUAL (BINARY-+ X Y) (BINARY-+ Y X)))

(DEFUN FIX (X) (IF (ACL2-NUMBERP X) X '0))

(DEFAXIOM UNICITY-OF-0 (EQUAL (BINARY-+ '0 X) (FIX X)))

(DEFAXIOM INVERSE-OF-+ (EQUAL (BINARY-+ X (UNARY-- X)) '0))

(DEFAXIOM ASSOCIATIVITY-OF-*
          (EQUAL (BINARY-* (BINARY-* X Y) Z)
                 (BINARY-* X (BINARY-* Y Z))))

(DEFAXIOM COMMUTATIVITY-OF-* (EQUAL (BINARY-* X Y) (BINARY-* Y X)))

(DEFAXIOM UNICITY-OF-1 (EQUAL (BINARY-* '1 X) (FIX X)))

(DEFAXIOM INVERSE-OF-*
          (IMPLIES (IF (ACL2-NUMBERP X)
                       (NOT (EQUAL X '0))
                       'NIL)
                   (EQUAL (BINARY-* X (UNARY-/ X)) '1)))

(DEFAXIOM DISTRIBUTIVITY
          (EQUAL (BINARY-* X (BINARY-+ Y Z))
                 (BINARY-+ (BINARY-* X Y)
                           (BINARY-* X Z))))

(DEFAXIOM <-ON-OTHERS (EQUAL (< X Y) (< (BINARY-+ X (UNARY-- Y)) '0)))

(DEFAXIOM ZERO (NOT (< '0 '0)))

(DEFAXIOM TRICHOTOMY
          (IF (IMPLIES (ACL2-NUMBERP X)
                       (IF (< '0 X)
                           (< '0 X)
                           (IF (EQUAL X '0)
                               (EQUAL X '0)
                               (< '0 (UNARY-- X)))))
              (IF (NOT (< '0 X))
                  (NOT (< '0 X))
                  (NOT (< '0 (UNARY-- X))))
              'NIL))

(DEFAXIOM POSITIVE
          (IF (IMPLIES (IF (< '0 X) (< '0 Y) 'NIL)
                       (< '0 (BINARY-+ X Y)))
              (IMPLIES (IF (RATIONALP X)
                           (IF (RATIONALP Y)
                               (IF (< '0 X) (< '0 Y) 'NIL)
                               'NIL)
                           'NIL)
                       (< '0 (BINARY-* X Y)))
              'NIL))

(DEFAXIOM RATIONAL-IMPLIES1
          (IMPLIES (RATIONALP X)
                   (IF (INTEGERP (DENOMINATOR X))
                       (IF (INTEGERP (NUMERATOR X))
                           (< '0 (DENOMINATOR X))
                           'NIL)
                       'NIL)))

(DEFAXIOM RATIONAL-IMPLIES2
          (IMPLIES (RATIONALP X)
                   (EQUAL (BINARY-* (UNARY-/ (DENOMINATOR X))
                                    (NUMERATOR X))
                          X)))

(DEFAXIOM INTEGER-IMPLIES-RATIONAL (IMPLIES (INTEGERP X) (RATIONALP X)))

(DEFAXIOM COMPLEX-IMPLIES1
          (IF (RATIONALP (REALPART X))
              (RATIONALP (IMAGPART X))
              'NIL))

(DEFAXIOM COMPLEX-DEFINITION
          (IMPLIES (IF (RATIONALP X) (RATIONALP Y) 'NIL)
                   (EQUAL (COMPLEX X Y)
                          (BINARY-+ X (BINARY-* '#C(0 1) Y)))))

(DEFAXIOM NONZERO-IMAGPART
          (IMPLIES (COMPLEX-RATIONALP X)
                   (NOT (EQUAL '0 (IMAGPART X)))))

(DEFAXIOM REALPART-IMAGPART-ELIM
          (IMPLIES (ACL2-NUMBERP X)
                   (EQUAL (COMPLEX (REALPART X) (IMAGPART X))
                          X)))

(DEFAXIOM REALPART-COMPLEX
          (IMPLIES (IF (RATIONALP X) (RATIONALP Y) 'NIL)
                   (EQUAL (REALPART (COMPLEX X Y)) X)))

(DEFAXIOM IMAGPART-COMPLEX
          (IMPLIES (IF (RATIONALP X) (RATIONALP Y) 'NIL)
                   (EQUAL (IMAGPART (COMPLEX X Y)) Y)))

(DEFTHM COMPLEX-EQUAL
        (IMPLIES (IF (RATIONALP X1)
                     (IF (RATIONALP Y1)
                         (IF (RATIONALP X2) (RATIONALP Y2) 'NIL)
                         'NIL)
                     'NIL)
                 (EQUAL (EQUAL (COMPLEX X1 Y1) (COMPLEX X2 Y2))
                        (IF (EQUAL X1 X2) (EQUAL Y1 Y2) 'NIL))))

(DEFUN FORCE (X) X)

(DEFUN IMMEDIATE-FORCE-MODEP NIL '"See :DOC immediate-force-modep.")

(DEFUN CASE-SPLIT (X) X)

(DEFUN SYNP (VARS FORM TERM) 'T)

(DEFUN EXTRA-INFO (X Y) 'T)

(DEFAXIOM NONNEGATIVE-PRODUCT
          (IMPLIES (RATIONALP X)
                   (IF (RATIONALP (BINARY-* X X))
                       (NOT (< (BINARY-* X X) '0))
                       'NIL)))

(DEFAXIOM INTEGER-0 (INTEGERP '0))

(DEFAXIOM INTEGER-1 (INTEGERP '1))

(DEFAXIOM INTEGER-STEP
          (IMPLIES (INTEGERP X)
                   (IF (INTEGERP (BINARY-+ X '1))
                       (INTEGERP (BINARY-+ X '-1))
                       'NIL)))

(DEFAXIOM
     LOWEST-TERMS
     (IMPLIES (IF (INTEGERP N)
                  (IF (RATIONALP X)
                      (IF (INTEGERP R)
                          (IF (INTEGERP Q)
                              (IF (< '0 N)
                                  (IF (EQUAL (NUMERATOR X) (BINARY-* N R))
                                      (EQUAL (DENOMINATOR X) (BINARY-* N Q))
                                      'NIL)
                                  'NIL)
                              'NIL)
                          'NIL)
                      'NIL)
                  'NIL)
              (EQUAL N '1)))

(DEFAXIOM CAR-CDR-ELIM (IMPLIES (CONSP X) (EQUAL (CONS (CAR X) (CDR X)) X)))

(DEFAXIOM CAR-CONS (EQUAL (CAR (CONS X Y)) X))

(DEFAXIOM CDR-CONS (EQUAL (CDR (CONS X Y)) Y))

(DEFAXIOM CONS-EQUAL
          (EQUAL (EQUAL (CONS X1 Y1) (CONS X2 Y2))
                 (IF (EQUAL X1 X2) (EQUAL Y1 Y2) 'NIL)))

(DEFAXIOM BOOLEANP-CHARACTERP (BOOLEANP (CHARACTERP X)))

(DEFAXIOM CHARACTERP-PAGE (CHARACTERP '#\Page))

(DEFAXIOM CHARACTERP-TAB (CHARACTERP '#\Tab))

(DEFAXIOM CHARACTERP-RUBOUT (CHARACTERP '#\Rubout))

(DEFUN MEMBER (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQL X (CAR L))
               L (MEMBER X (CDR L)))))

(DEFUN NO-DUPLICATESP (L)
       (IF (ENDP L)
           'T
           (IF (MEMBER (CAR L) (CDR L))
               'NIL
               (NO-DUPLICATESP (CDR L)))))

(DEFUN ASSOC (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQL X (CAR (CAR ALIST)))
               (CAR ALIST)
               (ASSOC X (CDR ALIST)))))

(DEFUN R-EQLABLE-ALISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (CONSP (CAR X))
               (IF (EQLABLEP (CDR (CAR X)))
                   (R-EQLABLE-ALISTP (CDR X))
                   'NIL)
               'NIL)))

(DEFUN RASSOC (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQL X (CDR (CAR ALIST)))
               (CAR ALIST)
               (RASSOC X (CDR ALIST)))))

(DEFUN RASSOC-EQUAL (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQUAL X (CDR (CAR ALIST)))
               (CAR ALIST)
               (RASSOC-EQUAL X (CDR ALIST)))))

(DEFUN R-SYMBOL-ALISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (CONSP (CAR X))
               (IF (SYMBOLP (CDR (CAR X)))
                   (R-SYMBOL-ALISTP (CDR X))
                   'NIL)
               'NIL)))

(DEFUN RASSOC-EQ (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQ X (CDR (CAR ALIST)))
               (CAR ALIST)
               (RASSOC-EQ X (CDR ALIST)))))

(DEFUN STANDARD-CHAR-P (X)
       (IF (MEMBER X
                   '(#\Newline #\Space #\! #\" #\# #\$ #\%
                               #\& #\' #\( #\) #\* #\+ #\, #\- #\. #\/
                               #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                               #\: #\; #\< #\= #\> #\? #\@ #\A #\B #\C
                               #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M
                               #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W
                               #\X #\Y #\Z #\[ #\\ #\] #\^ #\_ #\` #\a
                               #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k
                               #\l #\m #\n #\o #\p #\q #\r #\s #\t #\u
                               #\v #\w #\x #\y #\z #\{ #\| #\} #\~))
           'T
           'NIL))

(DEFUN STANDARD-CHAR-LISTP (L)
       (IF (CONSP L)
           (IF (CHARACTERP (CAR L))
               (IF (STANDARD-CHAR-P (CAR L))
                   (STANDARD-CHAR-LISTP (CDR L))
                   'NIL)
               'NIL)
           (EQUAL L 'NIL)))

(DEFUN CHARACTER-LISTP (L)
       (IF (ATOM L)
           (EQUAL L 'NIL)
           (IF (CHARACTERP (CAR L))
               (CHARACTER-LISTP (CDR L))
               'NIL)))

(DEFTHM CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP
        (IMPLIES (CHARACTER-LISTP X)
                 (EQLABLE-LISTP X)))

(DEFTHM STANDARD-CHAR-LISTP-FORWARD-TO-CHARACTER-LISTP
        (IMPLIES (STANDARD-CHAR-LISTP X)
                 (CHARACTER-LISTP X)))

(DEFAXIOM COERCE-INVERSE-1
          (IMPLIES (CHARACTER-LISTP X)
                   (EQUAL (COERCE (COERCE X 'STRING) 'LIST)
                          X)))

(DEFAXIOM COERCE-INVERSE-2
          (IMPLIES (STRINGP X)
                   (EQUAL (COERCE (COERCE X 'LIST) 'STRING)
                          X)))

(DEFAXIOM CHARACTER-LISTP-COERCE (CHARACTER-LISTP (COERCE STR 'LIST)))

(DEFUN STRING (X)
       (IF (STRINGP X)
           X
           (IF (SYMBOLP X)
               (SYMBOL-NAME X)
               (COERCE (CONS X 'NIL) 'STRING))))

(DEFUN ALPHA-CHAR-P (X)
       (IF (MEMBER X
                   '(#\a #\b #\c
                         #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
                         #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w
                         #\x #\y #\z #\A #\B #\C #\D #\E #\F #\G
                         #\H #\I #\J #\K #\L #\M #\N #\O #\P #\Q
                         #\R #\S #\T #\U #\V #\W #\X #\Y #\Z))
           'T
           'NIL))

(DEFUN UPPER-CASE-P (X)
       (IF (MEMBER X
                   '(#\A #\B #\C #\D #\E #\F #\G
                         #\H #\I #\J #\K #\L #\M #\N #\O #\P #\Q
                         #\R #\S #\T #\U #\V #\W #\X #\Y #\Z))
           'T
           'NIL))

(DEFUN LOWER-CASE-P (X)
       (IF (MEMBER X
                   '(#\a #\b #\c #\d #\e #\f #\g
                         #\h #\i #\j #\k #\l #\m #\n #\o #\p #\q
                         #\r #\s #\t #\u #\v #\w #\x #\y #\z))
           'T
           'NIL))

(DEFUN CHAR-UPCASE (X)
       ((LAMBDA (PAIR X)
                (IF PAIR (CDR PAIR)
                    (IF (CHARACTERP X) X (CODE-CHAR '0))))
        (ASSOC X
               '((#\a . #\A)
                 (#\b . #\B)
                 (#\c . #\C)
                 (#\d . #\D)
                 (#\e . #\E)
                 (#\f . #\F)
                 (#\g . #\G)
                 (#\h . #\H)
                 (#\i . #\I)
                 (#\j . #\J)
                 (#\k . #\K)
                 (#\l . #\L)
                 (#\m . #\M)
                 (#\n . #\N)
                 (#\o . #\O)
                 (#\p . #\P)
                 (#\q . #\Q)
                 (#\r . #\R)
                 (#\s . #\S)
                 (#\t . #\T)
                 (#\u . #\U)
                 (#\v . #\V)
                 (#\w . #\W)
                 (#\x . #\X)
                 (#\y . #\Y)
                 (#\z . #\Z)))
        X))

(DEFUN CHAR-DOWNCASE (X)
       ((LAMBDA (PAIR X)
                (IF PAIR (CDR PAIR)
                    (IF (CHARACTERP X) X (CODE-CHAR '0))))
        (ASSOC X
               '((#\A . #\a)
                 (#\B . #\b)
                 (#\C . #\c)
                 (#\D . #\d)
                 (#\E . #\e)
                 (#\F . #\f)
                 (#\G . #\g)
                 (#\H . #\h)
                 (#\I . #\i)
                 (#\J . #\j)
                 (#\K . #\k)
                 (#\L . #\l)
                 (#\M . #\m)
                 (#\N . #\n)
                 (#\O . #\o)
                 (#\P . #\p)
                 (#\Q . #\q)
                 (#\R . #\r)
                 (#\S . #\s)
                 (#\T . #\t)
                 (#\U . #\u)
                 (#\V . #\v)
                 (#\W . #\w)
                 (#\X . #\x)
                 (#\Y . #\y)
                 (#\Z . #\z)))
        X))

(DEFTHM LOWER-CASE-P-CHAR-DOWNCASE
        (IMPLIES (IF (UPPER-CASE-P X)
                     (CHARACTERP X)
                     'NIL)
                 (LOWER-CASE-P (CHAR-DOWNCASE X))))

(DEFTHM UPPER-CASE-P-CHAR-UPCASE
        (IMPLIES (IF (LOWER-CASE-P X)
                     (CHARACTERP X)
                     'NIL)
                 (UPPER-CASE-P (CHAR-UPCASE X))))

(DEFTHM LOWER-CASE-P-FORWARD-TO-ALPHA-CHAR-P
        (IMPLIES (IF (LOWER-CASE-P X)
                     (CHARACTERP X)
                     'NIL)
                 (ALPHA-CHAR-P X)))

(DEFTHM UPPER-CASE-P-FORWARD-TO-ALPHA-CHAR-P
        (IMPLIES (IF (UPPER-CASE-P X)
                     (CHARACTERP X)
                     'NIL)
                 (ALPHA-CHAR-P X)))

(DEFTHM ALPHA-CHAR-P-FORWARD-TO-CHARACTERP
        (IMPLIES (ALPHA-CHAR-P X)
                 (CHARACTERP X)))

(DEFTHM CHARACTERP-CHAR-DOWNCASE (CHARACTERP (CHAR-DOWNCASE X)))

(DEFTHM CHARACTERP-CHAR-UPCASE (CHARACTERP (CHAR-UPCASE X)))

(DEFUN STRING-DOWNCASE1 (L)
       (IF (ATOM L)
           'NIL
           (CONS (CHAR-DOWNCASE (CAR L))
                 (STRING-DOWNCASE1 (CDR L)))))

(DEFTHM CHARACTER-LISTP-STRING-DOWNCASE-1
        (CHARACTER-LISTP (STRING-DOWNCASE1 X)))

(DEFUN STRING-DOWNCASE (X)
       (COERCE (STRING-DOWNCASE1 (COERCE X 'LIST))
               'STRING))

(DEFUN STRING-UPCASE1 (L)
       (IF (ATOM L)
           'NIL
           (CONS (CHAR-UPCASE (CAR L))
                 (STRING-UPCASE1 (CDR L)))))

(DEFTHM CHARACTER-LISTP-STRING-UPCASE1-1
        (CHARACTER-LISTP (STRING-UPCASE1 X)))

(DEFUN STRING-UPCASE (X) (COERCE (STRING-UPCASE1 (COERCE X 'LIST)) 'STRING))

(DEFUN OUR-DIGIT-CHAR-P (CH RADIX)
       ((LAMBDA (L RADIX)
                (IF (IF L (< (CDR L) RADIX) 'NIL)
                    (CDR L)
                    'NIL))
        (ASSOC CH
               '((#\0 . 0)
                 (#\1 . 1)
                 (#\2 . 2)
                 (#\3 . 3)
                 (#\4 . 4)
                 (#\5 . 5)
                 (#\6 . 6)
                 (#\7 . 7)
                 (#\8 . 8)
                 (#\9 . 9)
                 (#\a . 10)
                 (#\b . 11)
                 (#\c . 12)
                 (#\d . 13)
                 (#\e . 14)
                 (#\f . 15)
                 (#\g . 16)
                 (#\h . 17)
                 (#\i . 18)
                 (#\j . 19)
                 (#\k . 20)
                 (#\l . 21)
                 (#\m . 22)
                 (#\n . 23)
                 (#\o . 24)
                 (#\p . 25)
                 (#\q . 26)
                 (#\r . 27)
                 (#\s . 28)
                 (#\t . 29)
                 (#\u . 30)
                 (#\v . 31)
                 (#\w . 32)
                 (#\x . 33)
                 (#\y . 34)
                 (#\z . 35)
                 (#\A . 10)
                 (#\B . 11)
                 (#\C . 12)
                 (#\D . 13)
                 (#\E . 14)
                 (#\F . 15)
                 (#\G . 16)
                 (#\H . 17)
                 (#\I . 18)
                 (#\J . 19)
                 (#\K . 20)
                 (#\L . 21)
                 (#\M . 22)
                 (#\N . 23)
                 (#\O . 24)
                 (#\P . 25)
                 (#\Q . 26)
                 (#\R . 27)
                 (#\S . 28)
                 (#\T . 29)
                 (#\U . 30)
                 (#\V . 31)
                 (#\W . 32)
                 (#\X . 33)
                 (#\Y . 34)
                 (#\Z . 35)))
        RADIX))

(DEFUN CHAR-EQUAL (X Y) (EQL (CHAR-DOWNCASE X) (CHAR-DOWNCASE Y)))

(DEFUN ATOM-LISTP (LST)
       (IF (ATOM LST)
           (EQ LST 'NIL)
           (IF (ATOM (CAR LST))
               (ATOM-LISTP (CDR LST))
               'NIL)))

(DEFTHM ATOM-LISTP-FORWARD-TO-TRUE-LISTP
        (IMPLIES (ATOM-LISTP X) (TRUE-LISTP X)))

(DEFTHM EQLABLE-LISTP-FORWARD-TO-ATOM-LISTP
        (IMPLIES (EQLABLE-LISTP X)
                 (ATOM-LISTP X)))

(DEFTHM CHARACTERP-NTH
        (IMPLIES (IF (CHARACTER-LISTP X)
                     (IF (INTEGERP I)
                         (IF (NOT (< I '0)) (< I (LEN X)) 'NIL)
                         'NIL)
                     'NIL)
                 (CHARACTERP (NTH I X))))

(DEFUN IFIX (X) (IF (INTEGERP X) X '0))

(DEFUN RFIX (X) (IF (RATIONALP X) X '0))

(DEFUN REALFIX (X) (IF (RATIONALP X) X '0))

(DEFUN NFIX (X) (IF (IF (INTEGERP X) (NOT (< X '0)) 'NIL) X '0))

(DEFUN STRING-EQUAL1 (STR1 STR2 I MAXIMUM)
       ((LAMBDA (I STR2 STR1 MAXIMUM)
                (IF (NOT (< I (IFIX MAXIMUM)))
                    'T
                    (IF (CHAR-EQUAL (CHAR STR1 I) (CHAR STR2 I))
                        (STRING-EQUAL1 STR1 STR2 (BINARY-+ '1 I)
                                       MAXIMUM)
                        'NIL)))
        (NFIX I)
        STR2 STR1 MAXIMUM))

(DEFUN STRING-EQUAL (STR1 STR2)
       ((LAMBDA (LEN1 STR1 STR2)
                (IF (= LEN1 (LENGTH STR2))
                    (STRING-EQUAL1 STR1 STR2 '0 LEN1)
                    'NIL))
        (LENGTH STR1)
        STR1 STR2))

(DEFUN STANDARD-STRING-ALISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (CONSP (CAR X))
               (IF (STRINGP (CAR (CAR X)))
                   (IF (STANDARD-CHAR-LISTP (COERCE (CAR (CAR X)) 'LIST))
                       (STANDARD-STRING-ALISTP (CDR X))
                       'NIL)
                   'NIL)
               'NIL)))

(DEFTHM STANDARD-STRING-ALISTP-FORWARD-TO-ALISTP
        (IMPLIES (STANDARD-STRING-ALISTP X)
                 (ALISTP X)))

(DEFUN ASSOC-STRING-EQUAL (STR ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (STRING-EQUAL STR (CAR (CAR ALIST)))
               (CAR ALIST)
               (ASSOC-STRING-EQUAL STR (CDR ALIST)))))

(DEFUN NATP (X) (IF (INTEGERP X) (NOT (< X '0)) 'NIL))

(DEFTHM NATP-COMPOUND-RECOGNIZER
        (EQUAL (NATP X)
               (IF (INTEGERP X) (NOT (< X '0)) 'NIL)))

(DEFUN POSP (X) (IF (INTEGERP X) (< '0 X) 'NIL))

(DEFTHM POSP-COMPOUND-RECOGNIZER
        (EQUAL (POSP X)
               (IF (INTEGERP X) (< '0 X) 'NIL)))

(DEFUN O-FINP (X) (ATOM X))

(DEFUN O-FIRST-EXPT (X) (IF (O-FINP X) '0 (CAR (CAR X))))

(DEFUN O-FIRST-COEFF (X) (IF (O-FINP X) X (CDR (CAR X))))

(DEFUN O-RST (X) (CDR X))

(DEFUN O<G (X)
       (IF (ATOM X)
           (RATIONALP X)
           (IF (CONSP (CAR X))
               (IF (RATIONALP (O-FIRST-COEFF X))
                   (IF (O<G (O-FIRST-EXPT X))
                       (O<G (O-RST X))
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN O< (X Y)
       (IF (O-FINP X)
           (IF (NOT (O-FINP Y))
               (NOT (O-FINP Y))
               (< X Y))
           (IF (O-FINP Y)
               'NIL
               (IF (NOT (EQUAL (O-FIRST-EXPT X)
                               (O-FIRST-EXPT Y)))
                   (O< (O-FIRST-EXPT X) (O-FIRST-EXPT Y))
                   (IF (NOT (= (O-FIRST-COEFF X) (O-FIRST-COEFF Y)))
                       (< (O-FIRST-COEFF X) (O-FIRST-COEFF Y))
                       (O< (O-RST X) (O-RST Y)))))))

(DEFUN O-P (X)
       (IF (O-FINP X)
           (NATP X)
           (IF (CONSP (CAR X))
               (IF (O-P (O-FIRST-EXPT X))
                   (IF (NOT (EQL '0 (O-FIRST-EXPT X)))
                       (IF (POSP (O-FIRST-COEFF X))
                           (IF (O-P (O-RST X))
                               (O< (O-FIRST-EXPT (O-RST X))
                                   (O-FIRST-EXPT X))
                               'NIL)
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)))

(DEFTHM O-P-IMPLIES-O<G (IMPLIES (O-P A) (O<G A)))

(DEFUN MAKE-ORD (FE FCO RST) (CONS (CONS FE FCO) RST))

(DEFUN LIST*-MACRO (LST)
       (IF (ENDP (CDR LST))
           (CAR LST)
           (CONS 'CONS
                 (CONS (CAR LST)
                       (CONS (LIST*-MACRO (CDR LST)) 'NIL)))))

(DEFUN NULL-BODY-ER (FN FORMALS)
       (CONS 'THROW-RAW-EV-FNCALL
             (CONS (CONS 'LIST
                         (CONS ''EV-FNCALL-NULL-BODY-ER
                               (CONS (CONS 'QUOTE (CONS FN 'NIL))
                                     FORMALS)))
                   'NIL)))

(DEFAXIOM STRINGP-SYMBOL-PACKAGE-NAME (STRINGP (SYMBOL-PACKAGE-NAME X)))

(DEFAXIOM SYMBOLP-INTERN-IN-PACKAGE-OF-SYMBOL
          (SYMBOLP (INTERN-IN-PACKAGE-OF-SYMBOL X Y)))

(DEFAXIOM SYMBOLP-PKG-WITNESS (SYMBOLP (PKG-WITNESS X)))

(DEFUN HARD-ERROR (CTX STR ALIST) 'NIL)

(DEFUN ILLEGAL (CTX STR ALIST) (HARD-ERROR CTX STR ALIST))

(DEFUN KEYWORDP (X)
       (IF (SYMBOLP X)
           (EQUAL (SYMBOL-PACKAGE-NAME X)
                  '"KEYWORD")
           'NIL))

(DEFTHM KEYWORDP-FORWARD-TO-SYMBOLP (IMPLIES (KEYWORDP X) (SYMBOLP X)))

(DEFAXIOM INTERN-IN-PACKAGE-OF-SYMBOL-SYMBOL-NAME
          (IMPLIES (IF (SYMBOLP X)
                       (EQUAL (SYMBOL-PACKAGE-NAME X)
                              (SYMBOL-PACKAGE-NAME Y))
                       'NIL)
                   (EQUAL (INTERN-IN-PACKAGE-OF-SYMBOL (SYMBOL-NAME X)
                                                       Y)
                          X)))

(DEFTHM SYMBOL-PACKAGE-NAME-OF-SYMBOL-IS-NOT-EMPTY-STRING
        (IMPLIES (SYMBOLP X)
                 (NOT (EQUAL (SYMBOL-PACKAGE-NAME X) '""))))

(DEFAXIOM SYMBOL-NAME-PKG-WITNESS
          (EQUAL (SYMBOL-NAME (PKG-WITNESS PKG-NAME))
                 '"ACL2-PKG-WITNESS"))

(DEFAXIOM SYMBOL-PACKAGE-NAME-PKG-WITNESS-NAME
          (EQUAL (SYMBOL-PACKAGE-NAME (PKG-WITNESS PKG-NAME))
                 (IF (IF (STRINGP PKG-NAME)
                         (NOT (EQUAL PKG-NAME '""))
                         'NIL)
                     PKG-NAME '"ACL2")))

(DEFUN MEMBER-SYMBOL-NAME (STR L)
       (IF (ENDP L)
           'NIL
           (IF (EQUAL STR (SYMBOL-NAME (CAR L)))
               L (MEMBER-SYMBOL-NAME STR (CDR L)))))

(DEFTHM SYMBOL-EQUALITY
        (IMPLIES (IF (SYMBOLP S1)
                     (IF (SYMBOLP S2)
                         (IF (EQUAL (SYMBOL-NAME S1)
                                    (SYMBOL-NAME S2))
                             (EQUAL (SYMBOL-PACKAGE-NAME S1)
                                    (SYMBOL-PACKAGE-NAME S2))
                             'NIL)
                         'NIL)
                     'NIL)
                 (EQUAL S1 S2)))

(DEFAXIOM
     SYMBOL-NAME-INTERN-IN-PACKAGE-OF-SYMBOL
     (IMPLIES (IF (STRINGP S)
                  (SYMBOLP ANY-SYMBOL)
                  'NIL)
              (EQUAL (SYMBOL-NAME (INTERN-IN-PACKAGE-OF-SYMBOL S ANY-SYMBOL))
                     S)))

(DEFAXIOM
     ACL2-INPUT-CHANNEL-PACKAGE
     (IMPLIES (IF (STRINGP X)
                  (IF (SYMBOLP Y)
                      (EQUAL (SYMBOL-PACKAGE-NAME Y)
                             '"ACL2-INPUT-CHANNEL")
                      'NIL)
                  'NIL)
              (EQUAL (SYMBOL-PACKAGE-NAME (INTERN-IN-PACKAGE-OF-SYMBOL X Y))
                     '"ACL2-INPUT-CHANNEL")))

(DEFAXIOM
     ACL2-OUTPUT-CHANNEL-PACKAGE
     (IMPLIES (IF (STRINGP X)
                  (IF (SYMBOLP Y)
                      (EQUAL (SYMBOL-PACKAGE-NAME Y)
                             '"ACL2-OUTPUT-CHANNEL")
                      'NIL)
                  'NIL)
              (EQUAL (SYMBOL-PACKAGE-NAME (INTERN-IN-PACKAGE-OF-SYMBOL X Y))
                     '"ACL2-OUTPUT-CHANNEL")))

(DEFAXIOM
 ACL2-PACKAGE
 (IMPLIES
  (IF
   (STRINGP X)
   (IF (NOT (MEMBER-SYMBOL-NAME
                 X
                 '(&ALLOW-OTHER-KEYS *PRINT-MISER-WIDTH*
                                     &AUX *PRINT-PPRINT-DISPATCH*
                                     &BODY *PRINT-PRETTY*
                                     &ENVIRONMENT *PRINT-RADIX*
                                     &KEY *PRINT-READABLY* &OPTIONAL
                                     *PRINT-RIGHT-MARGIN* &REST *QUERY-IO*
                                     &WHOLE *RANDOM-STATE* * *READ-BASE*
                                     ** *READ-DEFAULT-FLOAT-FORMAT*
                                     *** *READ-EVAL* *BREAK-ON-SIGNALS*
                                     *READ-SUPPRESS* *COMPILE-FILE-PATHNAME*
                                     *READTABLE* *COMPILE-FILE-TRUENAME*
                                     *STANDARD-INPUT* *COMPILE-PRINT*
                                     *STANDARD-OUTPUT* *COMPILE-VERBOSE*
                                     *TERMINAL-IO* *DEBUG-IO*
                                     *TRACE-OUTPUT* *DEBUGGER-HOOK*
                                     + *DEFAULT-PATHNAME-DEFAULTS*
                                     ++ *ERROR-OUTPUT* +++ *FEATURES*
                                     - *GENSYM-COUNTER* / *LOAD-PATHNAME*
                                     // *LOAD-PRINT* /// *LOAD-TRUENAME*
                                     /= *LOAD-VERBOSE* 1+ *MACROEXPAND-HOOK*
                                     1- *MODULES* < *PACKAGE*
                                     <= *PRINT-ARRAY* = *PRINT-BASE*
                                     > *PRINT-CASE* >= *PRINT-CIRCLE*
                                     ABORT *PRINT-ESCAPE* ABS *PRINT-GENSYM*
                                     ACONS *PRINT-LENGTH* ACOS *PRINT-LEVEL*
                                     ACOSH *PRINT-LINES* ADD-METHOD ADJOIN
                                     ATOM BOUNDP ADJUST-ARRAY BASE-CHAR
                                     BREAK ADJUSTABLE-ARRAY-P BASE-STRING
                                     BROADCAST-STREAM ALLOCATE-INSTANCE
                                     BIGNUM BROADCAST-STREAM-STREAMS
                                     ALPHA-CHAR-P BIT BUILT-IN-CLASS
                                     ALPHANUMERICP BIT-AND BUTLAST
                                     AND BIT-ANDC1 BYTE APPEND BIT-ANDC2
                                     BYTE-POSITION APPLY BIT-EQV BYTE-SIZE
                                     APROPOS BIT-IOR CAAAAR APROPOS-LIST
                                     BIT-NAND CAAADR AREF BIT-NOR
                                     CAAAR ARITHMETIC-ERROR BIT-NOT CAADAR
                                     ARITHMETIC-ERROR-OPERANDS BIT-ORC1
                                     CAADDR ARITHMETIC-ERROR-OPERATION
                                     BIT-ORC2 CAADR ARRAY BIT-VECTOR
                                     CAAR ARRAY-DIMENSION BIT-VECTOR-P
                                     CADAAR ARRAY-DIMENSION-LIMIT
                                     BIT-XOR CADADR ARRAY-DIMENSIONS
                                     BLOCK CADAR ARRAY-DISPLACEMENT
                                     BOOLE CADDAR ARRAY-ELEMENT-TYPE
                                     BOOLE-1 CADDDR ARRAY-HAS-FILL-POINTER-P
                                     BOOLE-2 CADDR ARRAY-IN-BOUNDS-P
                                     BOOLE-AND CADR ARRAY-RANK
                                     BOOLE-ANDC1 CALL-ARGUMENTS-LIMIT
                                     ARRAY-RANK-LIMIT BOOLE-ANDC2 CALL-METHOD
                                     ARRAY-ROW-MAJOR-INDEX BOOLE-C1
                                     CALL-NEXT-METHOD ARRAY-TOTAL-SIZE
                                     BOOLE-C2 CAR ARRAY-TOTAL-SIZE-LIMIT
                                     BOOLE-CLR CASE ARRAYP
                                     BOOLE-EQV CATCH ASH BOOLE-IOR CCASE
                                     ASIN BOOLE-NAND CDAAAR ASINH BOOLE-NOR
                                     CDAADR ASSERT BOOLE-ORC1 CDAAR ASSOC
                                     BOOLE-ORC2 CDADAR ASSOC-IF BOOLE-SET
                                     CDADDR ASSOC-IF-NOT BOOLE-XOR CDADR
                                     ATAN BOOLEAN CDAR ATANH BOTH-CASE-P
                                     CDDAAR CDDADR CLEAR-INPUT COPY-TREE
                                     CDDAR CLEAR-OUTPUT COS CDDDAR CLOSE COSH
                                     CDDDDR CLRHASH COUNT CDDDR CODE-CHAR
                                     COUNT-IF CDDR COERCE COUNT-IF-NOT
                                     CDR COMPILATION-SPEED CTYPECASE
                                     CEILING COMPILE DEBUG CELL-ERROR
                                     COMPILE-FILE DECF CELL-ERROR-NAME
                                     COMPILE-FILE-PATHNAME DECLAIM
                                     CERROR COMPILED-FUNCTION DECLARATION
                                     CHANGE-CLASS COMPILED-FUNCTION-P
                                     DECLARE CHAR COMPILER-MACRO DECODE-FLOAT
                                     CHAR-CODE COMPILER-MACRO-FUNCTION
                                     DECODE-UNIVERSAL-TIME
                                     CHAR-CODE-LIMIT COMPLEMENT DEFCLASS
                                     CHAR-DOWNCASE COMPLEX DEFCONSTANT
                                     CHAR-EQUAL COMPLEXP DEFGENERIC
                                     CHAR-GREATERP COMPUTE-APPLICABLE-METHODS
                                     DEFINE-COMPILER-MACRO
                                     CHAR-INT COMPUTE-RESTARTS
                                     DEFINE-CONDITION CHAR-LESSP
                                     CONCATENATE DEFINE-METHOD-COMBINATION
                                     CHAR-NAME CONCATENATED-STREAM
                                     DEFINE-MODIFY-MACRO CHAR-NOT-EQUAL
                                     CONCATENATED-STREAM-STREAMS
                                     DEFINE-SETF-EXPANDER CHAR-NOT-GREATERP
                                     COND DEFINE-SYMBOL-MACRO CHAR-NOT-LESSP
                                     CONDITION DEFMACRO CHAR-UPCASE CONJUGATE
                                     DEFMETHOD CHAR/= CONS DEFPACKAGE
                                     CHAR< CONSP DEFPARAMETER CHAR<=
                                     CONSTANTLY DEFSETF CHAR= CONSTANTP
                                     DEFSTRUCT CHAR> CONTINUE DEFTYPE
                                     CHAR>= CONTROL-ERROR DEFUN CHARACTER
                                     COPY-ALIST DEFVAR CHARACTERP COPY-LIST
                                     DELETE CHECK-TYPE COPY-PPRINT-DISPATCH
                                     DELETE-DUPLICATES CIS COPY-READTABLE
                                     DELETE-FILE CLASS COPY-SEQ DELETE-IF
                                     CLASS-NAME COPY-STRUCTURE DELETE-IF-NOT
                                     CLASS-OF COPY-SYMBOL DELETE-PACKAGE
                                     DENOMINATOR EQ DEPOSIT-FIELD
                                     EQL DESCRIBE EQUAL DESCRIBE-OBJECT
                                     EQUALP DESTRUCTURING-BIND
                                     ERROR DIGIT-CHAR ETYPECASE
                                     DIGIT-CHAR-P EVAL DIRECTORY EVAL-WHEN
                                     DIRECTORY-NAMESTRING EVENP DISASSEMBLE
                                     EVERY DIVISION-BY-ZERO EXP DO EXPORT
                                     DO* EXPT DO-ALL-SYMBOLS EXTENDED-CHAR
                                     DO-EXTERNAL-SYMBOLS FBOUNDP DO-SYMBOLS
                                     FCEILING DOCUMENTATION FDEFINITION
                                     DOLIST FFLOOR DOTIMES FIFTH DOUBLE-FLOAT
                                     FILE-AUTHOR DOUBLE-FLOAT-EPSILON
                                     FILE-ERROR DOUBLE-FLOAT-NEGATIVE-EPSILON
                                     FILE-ERROR-PATHNAME DPB FILE-LENGTH
                                     DRIBBLE FILE-NAMESTRING DYNAMIC-EXTENT
                                     FILE-POSITION ECASE FILE-STREAM
                                     ECHO-STREAM FILE-STRING-LENGTH
                                     ECHO-STREAM-INPUT-STREAM FILE-WRITE-DATE
                                     ECHO-STREAM-OUTPUT-STREAM
                                     FILL ED FILL-POINTER
                                     EIGHTH FIND ELT FIND-ALL-SYMBOLS
                                     ENCODE-UNIVERSAL-TIME FIND-CLASS
                                     END-OF-FILE FIND-IF ENDP FIND-IF-NOT
                                     ENOUGH-NAMESTRING FIND-METHOD
                                     ENSURE-DIRECTORIES-EXIST FIND-PACKAGE
                                     ENSURE-GENERIC-FUNCTION FIND-RESTART
                                     FIND-SYMBOL GET-INTERNAL-RUN-TIME
                                     FINISH-OUTPUT GET-MACRO-CHARACTER
                                     FIRST GET-OUTPUT-STREAM-STRING FIXNUM
                                     GET-PROPERTIES FLET GET-SETF-EXPANSION
                                     FLOAT GET-UNIVERSAL-TIME FLOAT-DIGITS
                                     GETF FLOAT-PRECISION GETHASH
                                     FLOAT-RADIX GO FLOAT-SIGN GRAPHIC-CHAR-P
                                     FLOATING-POINT-INEXACT HANDLER-BIND
                                     FLOATING-POINT-INVALID-OPERATION
                                     HANDLER-CASE FLOATING-POINT-OVERFLOW
                                     HASH-TABLE FLOATING-POINT-UNDERFLOW
                                     HASH-TABLE-COUNT FLOATP HASH-TABLE-P
                                     FLOOR HASH-TABLE-REHASH-SIZE FMAKUNBOUND
                                     HASH-TABLE-REHASH-THRESHOLD FORCE-OUTPUT
                                     HASH-TABLE-SIZE FORMAT HASH-TABLE-TEST
                                     FORMATTER HOST-NAMESTRING
                                     FOURTH IDENTITY FRESH-LINE
                                     IF FROUND IGNORABLE FTRUNCATE IGNORE
                                     FTYPE IGNORE-ERRORS FUNCALL IMAGPART
                                     FUNCTION IMPORT FUNCTION-KEYWORDS
                                     IN-PACKAGE FUNCTION-LAMBDA-EXPRESSION
                                     INCF FUNCTIONP INITIALIZE-INSTANCE
                                     GCD INLINE GENERIC-FUNCTION
                                     INPUT-STREAM-P GENSYM INSPECT
                                     GENTEMP INTEGER GET INTEGER-DECODE-FLOAT
                                     GET-DECODED-TIME INTEGER-LENGTH
                                     GET-DISPATCH-MACRO-CHARACTER
                                     INTEGERP GET-INTERNAL-REAL-TIME
                                     INTERACTIVE-STREAM-P
                                     INTERN LISP-IMPLEMENTATION-TYPE
                                     INTERNAL-TIME-UNITS-PER-SECOND
                                     LISP-IMPLEMENTATION-VERSION
                                     INTERSECTION LIST INVALID-METHOD-ERROR
                                     LIST* INVOKE-DEBUGGER
                                     LIST-ALL-PACKAGES INVOKE-RESTART
                                     LIST-LENGTH INVOKE-RESTART-INTERACTIVELY
                                     LISTEN ISQRT LISTP KEYWORD LOAD KEYWORDP
                                     LOAD-LOGICAL-PATHNAME-TRANSLATIONS
                                     LABELS LOAD-TIME-VALUE
                                     LAMBDA LOCALLY LAMBDA-LIST-KEYWORDS
                                     LOG LAMBDA-PARAMETERS-LIMIT
                                     LOGAND LAST LOGANDC1 LCM
                                     LOGANDC2 LDB LOGBITP LDB-TEST LOGCOUNT
                                     LDIFF LOGEQV LEAST-NEGATIVE-DOUBLE-FLOAT
                                     LOGICAL-PATHNAME
                                     LEAST-NEGATIVE-LONG-FLOAT
                                     LOGICAL-PATHNAME-TRANSLATIONS
                                     LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT
                                     LOGIOR
                                     LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT
                                     LOGNAND
                                     LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT
                                     LOGNOR
                                     LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT
                                     LOGNOT LEAST-NEGATIVE-SHORT-FLOAT
                                     LOGORC1 LEAST-NEGATIVE-SINGLE-FLOAT
                                     LOGORC2 LEAST-POSITIVE-DOUBLE-FLOAT
                                     LOGTEST LEAST-POSITIVE-LONG-FLOAT LOGXOR
                                     LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT
                                     LONG-FLOAT
                                     LEAST-POSITIVE-NORMALIZED-LONG-FLOAT
                                     LONG-FLOAT-EPSILON
                                     LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT
                                     LONG-FLOAT-NEGATIVE-EPSILON
                                     LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT
                                     LONG-SITE-NAME
                                     LEAST-POSITIVE-SHORT-FLOAT LOOP
                                     LEAST-POSITIVE-SINGLE-FLOAT LOOP-FINISH
                                     LENGTH LOWER-CASE-P LET MACHINE-INSTANCE
                                     LET* MACHINE-TYPE MACHINE-VERSION
                                     MASK-FIELD MACRO-FUNCTION
                                     MAX MACROEXPAND MEMBER MACROEXPAND-1
                                     MEMBER-IF MACROLET MEMBER-IF-NOT
                                     MAKE-ARRAY MERGE MAKE-BROADCAST-STREAM
                                     MERGE-PATHNAMES MAKE-CONCATENATED-STREAM
                                     METHOD MAKE-CONDITION METHOD-COMBINATION
                                     MAKE-DISPATCH-MACRO-CHARACTER
                                     METHOD-COMBINATION-ERROR
                                     MAKE-ECHO-STREAM METHOD-QUALIFIERS
                                     MAKE-HASH-TABLE MIN MAKE-INSTANCE
                                     MINUSP MAKE-INSTANCES-OBSOLETE
                                     MISMATCH MAKE-LIST MOD MAKE-LOAD-FORM
                                     MOST-NEGATIVE-DOUBLE-FLOAT
                                     MAKE-LOAD-FORM-SAVING-SLOTS
                                     MOST-NEGATIVE-FIXNUM
                                     MAKE-METHOD MOST-NEGATIVE-LONG-FLOAT
                                     MAKE-PACKAGE MOST-NEGATIVE-SHORT-FLOAT
                                     MAKE-PATHNAME MOST-NEGATIVE-SINGLE-FLOAT
                                     MAKE-RANDOM-STATE
                                     MOST-POSITIVE-DOUBLE-FLOAT
                                     MAKE-SEQUENCE MOST-POSITIVE-FIXNUM
                                     MAKE-STRING MOST-POSITIVE-LONG-FLOAT
                                     MAKE-STRING-INPUT-STREAM
                                     MOST-POSITIVE-SHORT-FLOAT
                                     MAKE-STRING-OUTPUT-STREAM
                                     MOST-POSITIVE-SINGLE-FLOAT
                                     MAKE-SYMBOL MUFFLE-WARNING
                                     MAKE-SYNONYM-STREAM MULTIPLE-VALUE-BIND
                                     MAKE-TWO-WAY-STREAM MULTIPLE-VALUE-CALL
                                     MAKUNBOUND MULTIPLE-VALUE-LIST
                                     MAP MULTIPLE-VALUE-PROG1
                                     MAP-INTO MULTIPLE-VALUE-SETQ MAPC
                                     MULTIPLE-VALUES-LIMIT MAPCAN NAME-CHAR
                                     MAPCAR NAMESTRING MAPCON NBUTLAST
                                     MAPHASH NCONC MAPL NEXT-METHOD-P
                                     MAPLIST NIL NINTERSECTION PACKAGE-ERROR
                                     NINTH PACKAGE-ERROR-PACKAGE
                                     NO-APPLICABLE-METHOD PACKAGE-NAME
                                     NO-NEXT-METHOD PACKAGE-NICKNAMES
                                     NOT PACKAGE-SHADOWING-SYMBOLS
                                     NOTANY PACKAGE-USE-LIST NOTEVERY
                                     PACKAGE-USED-BY-LIST NOTINLINE PACKAGEP
                                     NRECONC PAIRLIS NREVERSE PARSE-ERROR
                                     NSET-DIFFERENCE PARSE-INTEGER
                                     NSET-EXCLUSIVE-OR PARSE-NAMESTRING
                                     NSTRING-CAPITALIZE PATHNAME
                                     NSTRING-DOWNCASE PATHNAME-DEVICE
                                     NSTRING-UPCASE PATHNAME-DIRECTORY
                                     NSUBLIS PATHNAME-HOST NSUBST
                                     PATHNAME-MATCH-P NSUBST-IF PATHNAME-NAME
                                     NSUBST-IF-NOT PATHNAME-TYPE NSUBSTITUTE
                                     PATHNAME-VERSION NSUBSTITUTE-IF
                                     PATHNAMEP NSUBSTITUTE-IF-NOT
                                     PEEK-CHAR NTH PHASE NTH-VALUE PI NTHCDR
                                     PLUSP NULL POP NUMBER POSITION NUMBERP
                                     POSITION-IF NUMERATOR POSITION-IF-NOT
                                     NUNION PPRINT ODDP PPRINT-DISPATCH
                                     OPEN PPRINT-EXIT-IF-LIST-EXHAUSTED
                                     OPEN-STREAM-P PPRINT-FILL
                                     OPTIMIZE PPRINT-INDENT OR PPRINT-LINEAR
                                     OTHERWISE PPRINT-LOGICAL-BLOCK
                                     OUTPUT-STREAM-P PPRINT-NEWLINE
                                     PACKAGE PPRINT-POP PPRINT-TAB READ-CHAR
                                     PPRINT-TABULAR READ-CHAR-NO-HANG
                                     PRIN1 READ-DELIMITED-LIST
                                     PRIN1-TO-STRING READ-FROM-STRING
                                     PRINC READ-LINE PRINC-TO-STRING
                                     READ-PRESERVING-WHITESPACE
                                     PRINT READ-SEQUENCE PRINT-NOT-READABLE
                                     READER-ERROR PRINT-NOT-READABLE-OBJECT
                                     READTABLE PRINT-OBJECT
                                     READTABLE-CASE PRINT-UNREADABLE-OBJECT
                                     READTABLEP PROBE-FILE
                                     REAL PROCLAIM REALP PROG REALPART
                                     PROG* REDUCE PROG1 REINITIALIZE-INSTANCE
                                     PROG2 REM PROGN REMF PROGRAM-ERROR
                                     REMHASH PROGV REMOVE PROVIDE
                                     REMOVE-DUPLICATES PSETF REMOVE-IF
                                     PSETQ REMOVE-IF-NOT PUSH REMOVE-METHOD
                                     PUSHNEW REMPROP QUOTE RENAME-FILE
                                     RANDOM RENAME-PACKAGE RANDOM-STATE
                                     REPLACE RANDOM-STATE-P REQUIRE RASSOC
                                     REST RASSOC-IF RESTART RASSOC-IF-NOT
                                     RESTART-BIND RATIO RESTART-CASE
                                     RATIONAL RESTART-NAME RATIONALIZE RETURN
                                     RATIONALP RETURN-FROM READ REVAPPEND
                                     READ-BYTE REVERSE ROOM SIMPLE-BIT-VECTOR
                                     ROTATEF SIMPLE-BIT-VECTOR-P
                                     ROUND SIMPLE-CONDITION ROW-MAJOR-AREF
                                     SIMPLE-CONDITION-FORMAT-ARGUMENTS
                                     RPLACA SIMPLE-CONDITION-FORMAT-CONTROL
                                     RPLACD SIMPLE-ERROR
                                     SAFETY SIMPLE-STRING SATISFIES
                                     SIMPLE-STRING-P SBIT SIMPLE-TYPE-ERROR
                                     SCALE-FLOAT SIMPLE-VECTOR SCHAR
                                     SIMPLE-VECTOR-P SEARCH SIMPLE-WARNING
                                     SECOND SIN SEQUENCE SINGLE-FLOAT
                                     SERIOUS-CONDITION SINGLE-FLOAT-EPSILON
                                     SET SINGLE-FLOAT-NEGATIVE-EPSILON
                                     SET-DIFFERENCE
                                     SINH SET-DISPATCH-MACRO-CHARACTER
                                     SIXTH SET-EXCLUSIVE-OR
                                     SLEEP SET-MACRO-CHARACTER SLOT-BOUNDP
                                     SET-PPRINT-DISPATCH SLOT-EXISTS-P
                                     SET-SYNTAX-FROM-CHAR SLOT-MAKUNBOUND
                                     SETF SLOT-MISSING SETQ SLOT-UNBOUND
                                     SEVENTH SLOT-VALUE SHADOW SOFTWARE-TYPE
                                     SHADOWING-IMPORT SOFTWARE-VERSION
                                     SHARED-INITIALIZE SOME SHIFTF SORT
                                     SHORT-FLOAT SPACE SHORT-FLOAT-EPSILON
                                     SPECIAL SHORT-FLOAT-NEGATIVE-EPSILON
                                     SPECIAL-OPERATOR-P SHORT-SITE-NAME
                                     SPEED SIGNAL SQRT SIGNED-BYTE
                                     STABLE-SORT SIGNUM STANDARD SIMPLE-ARRAY
                                     STANDARD-CHAR SIMPLE-BASE-STRING
                                     STANDARD-CHAR-P STANDARD-CLASS
                                     SUBLIS STANDARD-GENERIC-FUNCTION SUBSEQ
                                     STANDARD-METHOD SUBSETP STANDARD-OBJECT
                                     SUBST STEP SUBST-IF STORAGE-CONDITION
                                     SUBST-IF-NOT STORE-VALUE SUBSTITUTE
                                     STREAM SUBSTITUTE-IF STREAM-ELEMENT-TYPE
                                     SUBSTITUTE-IF-NOT STREAM-ERROR
                                     SUBTYPEP STREAM-ERROR-STREAM
                                     SVREF STREAM-EXTERNAL-FORMAT
                                     SXHASH STREAMP SYMBOL
                                     STRING SYMBOL-FUNCTION STRING-CAPITALIZE
                                     SYMBOL-MACROLET STRING-DOWNCASE
                                     SYMBOL-NAME STRING-EQUAL SYMBOL-PACKAGE
                                     STRING-GREATERP SYMBOL-PLIST
                                     STRING-LEFT-TRIM SYMBOL-VALUE
                                     STRING-LESSP SYMBOLP STRING-NOT-EQUAL
                                     SYNONYM-STREAM STRING-NOT-GREATERP
                                     SYNONYM-STREAM-SYMBOL STRING-NOT-LESSP T
                                     STRING-RIGHT-TRIM TAGBODY STRING-STREAM
                                     TAILP STRING-TRIM TAN STRING-UPCASE
                                     TANH STRING/= TENTH STRING< TERPRI
                                     STRING<= THE STRING= THIRD STRING>
                                     THROW STRING>= TIME STRINGP TRACE
                                     STRUCTURE TRANSLATE-LOGICAL-PATHNAME
                                     STRUCTURE-CLASS
                                     TRANSLATE-PATHNAME STRUCTURE-OBJECT
                                     TREE-EQUAL STYLE-WARNING TRUENAME
                                     TRUNCATE VALUES-LIST TWO-WAY-STREAM
                                     VARIABLE TWO-WAY-STREAM-INPUT-STREAM
                                     VECTOR TWO-WAY-STREAM-OUTPUT-STREAM
                                     VECTOR-POP TYPE VECTOR-PUSH TYPE-ERROR
                                     VECTOR-PUSH-EXTEND TYPE-ERROR-DATUM
                                     VECTORP TYPE-ERROR-EXPECTED-TYPE
                                     WARN TYPE-OF WARNING TYPECASE
                                     WHEN TYPEP WILD-PATHNAME-P UNBOUND-SLOT
                                     WITH-ACCESSORS UNBOUND-SLOT-INSTANCE
                                     WITH-COMPILATION-UNIT
                                     UNBOUND-VARIABLE WITH-CONDITION-RESTARTS
                                     UNDEFINED-FUNCTION
                                     WITH-HASH-TABLE-ITERATOR
                                     UNEXPORT WITH-INPUT-FROM-STRING UNINTERN
                                     WITH-OPEN-FILE UNION WITH-OPEN-STREAM
                                     UNLESS WITH-OUTPUT-TO-STRING UNREAD-CHAR
                                     WITH-PACKAGE-ITERATOR UNSIGNED-BYTE
                                     WITH-SIMPLE-RESTART UNTRACE WITH-SLOTS
                                     UNUSE-PACKAGE WITH-STANDARD-IO-SYNTAX
                                     UNWIND-PROTECT WRITE
                                     UPDATE-INSTANCE-FOR-DIFFERENT-CLASS
                                     WRITE-BYTE
                                     UPDATE-INSTANCE-FOR-REDEFINED-CLASS
                                     WRITE-CHAR UPGRADED-ARRAY-ELEMENT-TYPE
                                     WRITE-LINE UPGRADED-COMPLEX-PART-TYPE
                                     WRITE-SEQUENCE UPPER-CASE-P
                                     WRITE-STRING USE-PACKAGE WRITE-TO-STRING
                                     USE-VALUE Y-OR-N-P USER-HOMEDIR-PATHNAME
                                     YES-OR-NO-P VALUES ZEROP)))
       (IF (SYMBOLP Y)
           (EQUAL (SYMBOL-PACKAGE-NAME Y) '"ACL2")
           'NIL)
       'NIL)
   'NIL)
  (EQUAL (SYMBOL-PACKAGE-NAME (INTERN-IN-PACKAGE-OF-SYMBOL X Y))
         '"ACL2")))

(DEFAXIOM
     KEYWORD-PACKAGE
     (IMPLIES (IF (STRINGP X)
                  (IF (SYMBOLP Y)
                      (EQUAL (SYMBOL-PACKAGE-NAME Y)
                             '"KEYWORD")
                      'NIL)
                  'NIL)
              (EQUAL (SYMBOL-PACKAGE-NAME (INTERN-IN-PACKAGE-OF-SYMBOL X Y))
                     '"KEYWORD")))

(DEFAXIOM
  STRING-IS-NOT-CIRCULAR
  (EQUAL 'STRING
         (INTERN-IN-PACKAGE-OF-SYMBOL
              (COERCE (CONS '#\S
                            (CONS '#\T
                                  (CONS '#\R
                                        (CONS '#\I
                                              (CONS '#\N (CONS '#\G '0))))))
                      (CONS '#\S
                            (CONS '#\T
                                  (CONS '#\R
                                        (CONS '#\I
                                              (CONS '#\N (CONS '#\G '0)))))))
              (INTERN-IN-PACKAGE-OF-SYMBOL '0 '0))))

(DEFAXIOM
 NIL-IS-NOT-CIRCULAR
 (EQUAL
  'NIL
  (INTERN-IN-PACKAGE-OF-SYMBOL (COERCE (CONS '#\N (CONS '#\I (CONS '#\L '0)))
                                       'STRING)
                               'STRING)))

(DEFUN BINARY-APPEND (X Y)
       (IF (ENDP X)
           Y
           (CONS (CAR X)
                 (BINARY-APPEND (CDR X) Y))))

(DEFTHM STANDARD-CHAR-LISTP-APPEND
        (IMPLIES (TRUE-LISTP X)
                 (EQUAL (STANDARD-CHAR-LISTP (BINARY-APPEND X Y))
                        (IF (STANDARD-CHAR-LISTP X)
                            (STANDARD-CHAR-LISTP Y)
                            'NIL))))

(DEFTHM CHARACTER-LISTP-APPEND
        (IMPLIES (TRUE-LISTP X)
                 (EQUAL (CHARACTER-LISTP (BINARY-APPEND X Y))
                        (IF (CHARACTER-LISTP X)
                            (CHARACTER-LISTP Y)
                            'NIL))))

(DEFTHM APPEND-TO-NIL
        (IMPLIES (TRUE-LISTP X)
                 (EQUAL (BINARY-APPEND X 'NIL) X)))

(DEFUN STRING-APPEND (STR1 STR2)
       (MUST-BE-EQUAL (COERCE (BINARY-APPEND (COERCE STR1 'LIST)
                                             (COERCE STR2 'LIST))
                              'STRING)
                      (STRING-APPEND STR1 STR2)))

(DEFUN STRING-LISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (STRINGP (CAR X))
               (STRING-LISTP (CDR X))
               'NIL)))

(DEFUN STRING-APPEND-LST (X)
       (IF (ENDP X)
           '""
           (STRING-APPEND (CAR X)
                          (STRING-APPEND-LST (CDR X)))))

(DEFUN REMOVE (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQL X (CAR L))
               (REMOVE X (CDR L))
               (CONS (CAR L) (REMOVE X (CDR L))))))

(DEFUN REMOVE-EQ (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQ X (CAR L))
               (REMOVE-EQ X (CDR L))
               (CONS (CAR L) (REMOVE-EQ X (CDR L))))))

(DEFUN REMOVE-EQUAL (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQUAL X (CAR L))
               (REMOVE-EQUAL X (CDR L))
               (CONS (CAR L)
                     (REMOVE-EQUAL X (CDR L))))))

(DEFUN REMOVE1 (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQL X (CAR L))
               (CDR L)
               (CONS (CAR L) (REMOVE1 X (CDR L))))))

(DEFUN REMOVE1-EQ (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQ X (CAR L))
               (CDR L)
               (CONS (CAR L) (REMOVE1-EQ X (CDR L))))))

(DEFUN REMOVE1-EQUAL (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQUAL X (CAR L))
               (CDR L)
               (CONS (CAR L)
                     (REMOVE1-EQUAL X (CDR L))))))

(DEFUN PAIRLIS$ (X Y)
       (IF (ENDP X)
           'NIL
           (CONS (CONS (CAR X) (CAR Y))
                 (PAIRLIS$ (CDR X) (CDR Y)))))

(DEFUN REMOVE-DUPLICATES-EQL (L)
       (IF (ENDP L)
           'NIL
           (IF (MEMBER (CAR L) (CDR L))
               (REMOVE-DUPLICATES-EQL (CDR L))
               (CONS (CAR L)
                     (REMOVE-DUPLICATES-EQL (CDR L))))))

(DEFTHM CHARACTER-LISTP-REMOVE-DUPLICATES-EQL
        (IMPLIES (CHARACTER-LISTP X)
                 (CHARACTER-LISTP (REMOVE-DUPLICATES-EQL X))))

(DEFUN REMOVE-DUPLICATES (L)
       (IF (STRINGP L)
           (COERCE (REMOVE-DUPLICATES-EQL (COERCE L 'LIST))
                   'STRING)
           (REMOVE-DUPLICATES-EQL L)))

(DEFUN REMOVE-DUPLICATES-EQUAL (L)
       (IF (ENDP L)
           'NIL
           (IF (MEMBER-EQUAL (CAR L) (CDR L))
               (REMOVE-DUPLICATES-EQUAL (CDR L))
               (CONS (CAR L)
                     (REMOVE-DUPLICATES-EQUAL (CDR L))))))

(DEFUN IDENTITY (X) X)

(DEFUN REVAPPEND (X Y) (IF (ENDP X) Y (REVAPPEND (CDR X) (CONS (CAR X) Y))))

(DEFTHM CHARACTER-LISTP-REVAPPEND
        (IMPLIES (TRUE-LISTP X)
                 (EQUAL (CHARACTER-LISTP (REVAPPEND X Y))
                        (IF (CHARACTER-LISTP X)
                            (CHARACTER-LISTP Y)
                            'NIL))))

(DEFUN REVERSE (X)
       (IF (STRINGP X)
           (COERCE (REVAPPEND (COERCE X 'LIST) 'NIL)
                   'STRING)
           (REVAPPEND X 'NIL)))

(DEFUN SET-DIFFERENCE-EQ (L1 L2)
       (IF (ENDP L1)
           'NIL
           (IF (MEMBER-EQ (CAR L1) L2)
               (SET-DIFFERENCE-EQ (CDR L1) L2)
               (CONS (CAR L1)
                     (SET-DIFFERENCE-EQ (CDR L1) L2)))))

(DEFUN LISTP (X) (IF (CONSP X) (CONSP X) (EQUAL X 'NIL)))

(DEFUN LAST (L) (IF (ATOM (CDR L)) L (LAST (CDR L))))

(DEFUN FIRST-N-AC (I L AC)
       (IF (ZP I)
           (REVERSE AC)
           (FIRST-N-AC (BINARY-+ '-1 I)
                       (CDR L)
                       (CONS (CAR L) AC))))

(DEFUN TAKE (N L) (FIRST-N-AC N L 'NIL))

(DEFUN BUTLAST (LST N)
       ((LAMBDA (LNG LST N)
                (IF (NOT (< N LNG))
                    'NIL
                    (TAKE (BINARY-+ LNG (UNARY-- N)) LST)))
        (LEN LST)
        LST N))

(DEFUN STRIP-CDRS (X)
       (IF (ENDP X)
           'NIL
           (CONS (CDR (CAR X))
                 (STRIP-CDRS (CDR X)))))

(DEFUN MUTUAL-RECURSION-GUARDP (RST)
       (IF (ATOM RST)
           (EQUAL RST 'NIL)
           (IF (CONSP (CAR RST))
               (IF (TRUE-LISTP (CAR RST))
                   (IF (MEMBER-EQ (CAR (CAR RST))
                                  '(DEFUN DEFUND))
                       (MUTUAL-RECURSION-GUARDP (CDR RST))
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN COLLECT-CADRS-WHEN-CAR-EQ (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQ X (CAR (CAR ALIST)))
               (CONS (CAR (CDR (CAR ALIST)))
                     (COLLECT-CADRS-WHEN-CAR-EQ X (CDR ALIST)))
               (COLLECT-CADRS-WHEN-CAR-EQ X (CDR ALIST)))))

(DEFUN
 VALUE-TRIPLE-FN
 (FORM ON-SKIP-PROOFS CHECK)
 (CONS
  'COND
  (CONS
   (CONS (CONS 'AND
               (CONS (NOT ON-SKIP-PROOFS)
                     (CONS (CONS 'F-GET-GLOBAL
                                 (CONS (CONS 'QUOTE
                                             (CONS 'LD-SKIP-PROOFSP 'NIL))
                                       (CONS 'STATE 'NIL)))
                           'NIL)))
         (CONS (CONS 'VALUE (CONS ':SKIPPED 'NIL))
               'NIL))
   (CONS
    (CONS
     'T
     (CONS
      ((LAMBDA (FORM)
               (CONS 'STATE-GLOBAL-LET*
                     (CONS (CONS (CONS 'SAFE-MODE (CONS 'T 'NIL))
                                 'NIL)
                           (CONS (CONS 'VALUE (CONS FORM 'NIL))
                                 'NIL))))
       (CONS
        'LET
        (CONS
         (CONS (CONS 'CHECK (CONS CHECK 'NIL))
               'NIL)
         (CONS
          (CONS
           'COND
           (CONS
            (CONS
             'CHECK
             (CONS
              (CONS
               'COND
               (CONS
                (CONS (CONS 'CHECK-VARS-NOT-FREE
                            (CONS (CONS 'CHECK 'NIL)
                                  (CONS FORM 'NIL)))
                      (CONS ':PASSED 'NIL))
                (CONS
                 (CONS
                  (CONS 'TILDE-@P (CONS 'CHECK 'NIL))
                  (CONS
                    (CONS 'ER
                          (CONS 'HARD
                                (CONS (CONS 'QUOTE (CONS 'VALUE-TRIPLE 'NIL))
                                      (CONS '"Assertion failed:~%~@0~|"
                                            (CONS 'CHECK 'NIL)))))
                    'NIL))
                 (CONS
                  (CONS
                   'T
                   (CONS
                    (CONS
                       'ER
                       (CONS 'HARD
                             (CONS (CONS 'QUOTE (CONS 'VALUE-TRIPLE 'NIL))
                                   (CONS '"Assertion failed on form:~%~x0~|"
                                         (CONS (CONS 'QUOTE (CONS FORM 'NIL))
                                               'NIL)))))
                    'NIL))
                  'NIL))))
              'NIL))
            (CONS (CONS 'T (CONS FORM 'NIL)) 'NIL)))
          'NIL))))
      'NIL))
    'NIL))))

(DEFUN XD-NAME (EVENT-TYPE NAME)
       (IF (EQ EVENT-TYPE 'DEFUND)
           (CONS ':DEFUND (CONS NAME 'NIL))
           (IF (EQ EVENT-TYPE 'DEFTHMD)
               (CONS ':DEFTHMD (CONS NAME 'NIL))
               (ILLEGAL 'XD-NAME
                        '"Unexpected event-type for xd-name, ~x0"
                        (CONS (CONS '#\0 EVENT-TYPE) 'NIL)))))

(DEFUN DEFUND-NAME-LIST (DEFUNS ACC)
       (IF (ENDP DEFUNS)
           (REVERSE ACC)
           (DEFUND-NAME-LIST (CDR DEFUNS)
                             (CONS (IF (EQ (CAR (CAR DEFUNS)) 'DEFUND)
                                       (XD-NAME 'DEFUND
                                                (CAR (CDR (CAR DEFUNS))))
                                       (CAR (CDR (CAR DEFUNS))))
                                   ACC))))

(MUTUAL-RECURSION
 (DEFUN
  PSEUDO-TERMP (X)
  (IF
   (ATOM X)
   (SYMBOLP X)
   (IF
     (EQ (CAR X) 'QUOTE)
     (IF (CONSP (CDR X))
         (NULL (CDR (CDR X)))
         'NIL)
     (IF (NOT (TRUE-LISTP X))
         'NIL
         (IF (NOT (PSEUDO-TERM-LISTP (CDR X)))
             'NIL
             (IF (SYMBOLP (CAR X))
                 (SYMBOLP (CAR X))
                 (IF (TRUE-LISTP (CAR X))
                     (IF (EQUAL (LENGTH (CAR X)) '3)
                         (IF (EQ (CAR (CAR X)) 'LAMBDA)
                             (IF (SYMBOL-LISTP (CAR (CDR (CAR X))))
                                 (IF (PSEUDO-TERMP (CAR (CDR (CDR (CAR X)))))
                                     (EQUAL (LENGTH (CAR (CDR (CAR X))))
                                            (LENGTH (CDR X)))
                                     'NIL)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)))))))
 (DEFUN PSEUDO-TERM-LISTP (LST)
        (IF (ATOM LST)
            (EQUAL LST 'NIL)
            (IF (PSEUDO-TERMP (CAR LST))
                (PSEUDO-TERM-LISTP (CDR LST))
                'NIL))))

(DEFTHM PSEUDO-TERM-LISTP-FORWARD-TO-TRUE-LISTP
        (IMPLIES (PSEUDO-TERM-LISTP X)
                 (TRUE-LISTP X)))

(DEFUN PSEUDO-TERM-LIST-LISTP (L)
       (IF (ATOM L)
           (EQUAL L 'NIL)
           (IF (PSEUDO-TERM-LISTP (CAR L))
               (PSEUDO-TERM-LIST-LISTP (CDR L))
               'NIL)))

(DEFUN ADD-TO-SET-EQ (X LST) (IF (MEMBER-EQ X LST) LST (CONS X LST)))

(DEFUN ADD-TO-SET-EQL (X LST) (IF (MEMBER X LST) LST (CONS X LST)))

(DEFUN QUOTEP (X) (IF (CONSP X) (EQ (CAR X) 'QUOTE) 'NIL))

(DEFUN KWOTE (X) (CONS 'QUOTE (CONS X 'NIL)))

(DEFUN KWOTE-LST (LST)
       (IF (ENDP LST)
           'NIL
           (CONS (KWOTE (CAR LST))
                 (KWOTE-LST (CDR LST)))))

(DEFUN FN-SYMB (X)
       (IF (IF (CONSP X)
               (NOT (EQ 'QUOTE (CAR X)))
               'NIL)
           (CAR X)
           'NIL))

(MUTUAL-RECURSION (DEFUN ALL-VARS1 (TERM ANS)
                         (IF (ATOM TERM)
                             (ADD-TO-SET-EQ TERM ANS)
                             (IF (EQ 'QUOTE (CAR TERM))
                                 ANS (ALL-VARS1-LST (CDR TERM) ANS))))
                  (DEFUN ALL-VARS1-LST (LST ANS)
                         (IF (ENDP LST)
                             ANS
                             (ALL-VARS1-LST (CDR LST)
                                            (ALL-VARS1 (CAR LST) ANS)))))

(DEFUN ALL-VARS (TERM) (ALL-VARS1 TERM 'NIL))

(DEFUN INTERSECTP-EQ (X Y)
       (IF (ENDP X)
           'NIL
           (IF (MEMBER-EQ (CAR X) Y)
               'T
               (INTERSECTP-EQ (CDR X) Y))))

(DEFUN INTERSECTP (X Y)
       (IF (ENDP X)
           'NIL
           (IF (MEMBER (CAR X) Y)
               'T
               (INTERSECTP (CDR X) Y))))

(DEFUN INTERSECTP-EQUAL (X Y)
       (IF (ENDP X)
           'NIL
           (IF (MEMBER-EQUAL (CAR X) Y)
               'T
               (INTERSECTP-EQUAL (CDR X) Y))))

(DEFUN MAKE-FMT-BINDINGS (CHARS FORMS)
       (IF (ENDP FORMS)
           'NIL
           (CONS 'CONS
                 (CONS (CONS 'CONS
                             (CONS (CAR CHARS)
                                   (CONS (CAR FORMS) 'NIL)))
                       (CONS (MAKE-FMT-BINDINGS (CDR CHARS)
                                                (CDR FORMS))
                             'NIL)))))

(DEFUN
 ER-PROGN-FN (LST)
 (IF
  (ENDP LST)
  'NIL
  (IF
   (ENDP (CDR LST))
   (CAR LST)
   (CONS
    'MV-LET
    (CONS
     '(ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP
           ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-VAL
           STATE)
     (CONS
      (CAR LST)
      (CONS
       '(DECLARE (IGNORABLE ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-VAL))
       (CONS
        (CONS
         'IF
         (CONS
          'ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP
          (CONS
               '(MV ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP
                    ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-VAL
                    STATE)
               (CONS (CONS 'CHECK-VARS-NOT-FREE
                           (CONS '(ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP
                                       ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-VAL)
                                 (CONS (ER-PROGN-FN (CDR LST)) 'NIL)))
                     'NIL))))
        'NIL))))))))

(DEFUN LEGAL-CASE-CLAUSESP (TL)
       (IF (ATOM TL)
           (EQ TL 'NIL)
           (IF (IF (CONSP (CAR TL))
                   (IF (IF (EQLABLEP (CAR (CAR TL)))
                           (EQLABLEP (CAR (CAR TL)))
                           (EQLABLE-LISTP (CAR (CAR TL))))
                       (IF (CONSP (CDR (CAR TL)))
                           (IF (NULL (CDR (CDR (CAR TL))))
                               (IF (IF (EQ 'T (CAR (CAR TL)))
                                       (EQ 'T (CAR (CAR TL)))
                                       (EQ 'OTHERWISE (CAR (CAR TL))))
                                   (NULL (CDR TL))
                                   'T)
                               'NIL)
                           'NIL)
                       'NIL)
                   'NIL)
               (LEGAL-CASE-CLAUSESP (CDR TL))
               'NIL)))

(DEFUN CASE-TEST (X PAT)
       (IF (ATOM PAT)
           (CONS 'EQL
                 (CONS X
                       (CONS (CONS 'QUOTE (CONS PAT 'NIL))
                             'NIL)))
           (CONS 'MEMBER
                 (CONS X
                       (CONS (CONS 'QUOTE (CONS PAT 'NIL))
                             'NIL)))))

(DEFUN CASE-LIST (X L)
       (IF (ENDP L)
           'NIL
           (IF (IF (EQ 'T (CAR (CAR L)))
                   (EQ 'T (CAR (CAR L)))
                   (EQ 'OTHERWISE (CAR (CAR L))))
               (CONS (CONS 'T
                           (CONS (CAR (CDR (CAR L))) 'NIL))
                     'NIL)
               (IF (NULL (CAR (CAR L)))
                   (CASE-LIST X (CDR L))
                   (CONS (CONS (CASE-TEST X (CAR (CAR L)))
                               (CONS (CAR (CDR (CAR L))) 'NIL))
                         (CASE-LIST X (CDR L)))))))

(DEFUN
  CASE-LIST-CHECK (L)
  (IF (ENDP L)
      'NIL
      (IF (IF (EQ 'T (CAR (CAR L)))
              (EQ 'T (CAR (CAR L)))
              (EQ 'OTHERWISE (CAR (CAR L))))
          (CONS (CONS 'T
                      (CONS (CONS 'CHECK-VARS-NOT-FREE
                                  (CONS '(CASE-DO-NOT-USE-ELSEWHERE)
                                        (CONS (CAR (CDR (CAR L))) 'NIL)))
                            'NIL))
                'NIL)
          (IF (NULL (CAR (CAR L)))
              (CASE-LIST-CHECK (CDR L))
              (CONS (CONS (CASE-TEST 'CASE-DO-NOT-USE-ELSEWHERE
                                     (CAR (CAR L)))
                          (CONS (CONS 'CHECK-VARS-NOT-FREE
                                      (CONS '(CASE-DO-NOT-USE-ELSEWHERE)
                                            (CONS (CAR (CDR (CAR L))) 'NIL)))
                                'NIL))
                    (CASE-LIST-CHECK (CDR L)))))))

(DEFUN POSITION-EQUAL-AC (ITEM LST ACC)
       (IF (ENDP LST)
           'NIL
           (IF (EQUAL ITEM (CAR LST))
               ACC
               (POSITION-EQUAL-AC ITEM (CDR LST)
                                  (BINARY-+ '1 ACC)))))

(DEFUN POSITION-AC (ITEM LST ACC)
       (IF (ENDP LST)
           'NIL
           (IF (EQL ITEM (CAR LST))
               ACC
               (POSITION-AC ITEM (CDR LST)
                            (BINARY-+ '1 ACC)))))

(DEFUN POSITION-EQUAL (ITEM LST)
       (IF (STRINGP LST)
           (POSITION-AC ITEM (COERCE LST 'LIST) '0)
           (POSITION-EQUAL-AC ITEM LST '0)))

(DEFUN POSITION-EQ-AC (ITEM LST ACC)
       (IF (ENDP LST)
           'NIL
           (IF (EQ ITEM (CAR LST))
               ACC
               (POSITION-EQ-AC ITEM (CDR LST)
                               (BINARY-+ '1 ACC)))))

(DEFUN POSITION-EQ (ITEM LST) (POSITION-EQ-AC ITEM LST '0))

(DEFUN POSITION (ITEM LST)
       (IF (STRINGP LST)
           (POSITION-AC ITEM (COERCE LST 'LIST) '0)
           (POSITION-AC ITEM LST '0)))

(DEFUN NONNEGATIVE-INTEGER-QUOTIENT (I J)
       (IF (IF (= (NFIX J) '0)
               (= (NFIX J) '0)
               (< (IFIX I) J))
           '0
           (BINARY-+ '1
                     (NONNEGATIVE-INTEGER-QUOTIENT (BINARY-+ I (UNARY-- J))
                                                   J))))

(DEFUN TRUE-LIST-LISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (TRUE-LISTP (CAR X))
               (TRUE-LIST-LISTP (CDR X))
               'NIL)))

(DEFTHM TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP
        (IMPLIES (TRUE-LIST-LISTP X)
                 (TRUE-LISTP X)))

(DEFUN
 LEGAL-LET*-P
 (BINDINGS IGNORE-VARS IGNORED-SEEN TOP-FORM)
 (IF
  (ENDP BINDINGS)
  (IF
   (EQ IGNORE-VARS 'NIL)
   (EQ IGNORE-VARS 'NIL)
   (HARD-ERROR
    'LET*
    '"All variables declared IGNOREd or IGNORABLE in a ~
                          LET* form must be bound, but ~&0 ~#0~[is~/are~] not ~
                          bound in the form ~x1."
    (CONS (CONS '#\0 IGNORE-VARS)
          (CONS (CONS '#\1 TOP-FORM) 'NIL))))
  (IF
   (MEMBER-EQ (CAR (CAR BINDINGS))
              IGNORED-SEEN)
   (HARD-ERROR
    'LET*
    '"A variable bound more than once in a LET* form may not ~
                      be declared IGNOREd or IGNORABLE, but the variable ~x0 ~
                      is bound more than once in form ~x1 and yet is so ~
                      declared."
    (CONS (CONS '#\0 (CAR (CAR BINDINGS)))
          (CONS (CONS '#\1 TOP-FORM) 'NIL)))
   (IF (MEMBER-EQ (CAR (CAR BINDINGS))
                  IGNORE-VARS)
       (LEGAL-LET*-P (CDR BINDINGS)
                     (REMOVE (CAR (CAR BINDINGS))
                             IGNORE-VARS)
                     (CONS (CAR (CAR BINDINGS)) IGNORED-SEEN)
                     TOP-FORM)
       (LEGAL-LET*-P (CDR BINDINGS)
                     IGNORE-VARS IGNORED-SEEN TOP-FORM)))))

(DEFUN WELL-FORMED-TYPE-DECLS-P (DECLS VARS)
       (IF (ENDP DECLS)
           'T
           (IF (SUBSETP-EQ (CDR (CDR (CAR DECLS)))
                           VARS)
               (WELL-FORMED-TYPE-DECLS-P (CDR DECLS)
                                         VARS)
               'NIL)))

(DEFUN SYMBOL-LIST-LISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (SYMBOL-LISTP (CAR X))
               (SYMBOL-LIST-LISTP (CDR X))
               'NIL)))

(DEFUN GET-TYPE-DECLS (VAR TYPE-DECLS)
       (IF (ENDP TYPE-DECLS)
           'NIL
           (IF (MEMBER-EQ VAR (CDR (CAR TYPE-DECLS)))
               (CONS (CONS 'TYPE
                           (CONS (CAR (CAR TYPE-DECLS))
                                 (CONS VAR 'NIL)))
                     (GET-TYPE-DECLS VAR (CDR TYPE-DECLS)))
               (GET-TYPE-DECLS VAR (CDR TYPE-DECLS)))))

(DEFUN
 LET*-MACRO
 (BINDINGS IGNORE-VARS
           IGNORABLE-VARS TYPE-DECLS BODY)
 (IF
  (ENDP BINDINGS)
  (PROG2$
   (IF
    (NULL IGNORE-VARS)
    (NULL IGNORE-VARS)
    (HARD-ERROR
     'LET*-MACRO
     '"Implementation error: Ignored variables ~x0 ~
                                  must be bound in superior LET* form!"
     IGNORE-VARS))
   (PROG2$
    (IF
     (NULL IGNORABLE-VARS)
     (NULL IGNORABLE-VARS)
     (HARD-ERROR
      'LET*-MACRO
      '"Implementation error: Ignorable ~
                                          variables ~x0 must be bound in ~
                                          superior LET* form!"
      IGNORABLE-VARS))
    BODY))
  (CONS
   'LET
   (CONS
    (CONS (CAR BINDINGS) 'NIL)
    ((LAMBDA
      (REST TYPE-DECLS
            IGNORABLE-VARS IGNORE-VARS BINDINGS)
      (BINARY-APPEND
        (IF (MEMBER-EQ (CAR (CAR BINDINGS))
                       IGNORE-VARS)
            (CONS (CONS 'DECLARE
                        (CONS (CONS 'IGNORE
                                    (CONS (CAR (CAR BINDINGS)) 'NIL))
                              'NIL))
                  'NIL)
            'NIL)
        (BINARY-APPEND
             (IF (MEMBER-EQ (CAR (CAR BINDINGS))
                            IGNORABLE-VARS)
                 (CONS (CONS 'DECLARE
                             (CONS (CONS 'IGNORABLE
                                         (CONS (CAR (CAR BINDINGS)) 'NIL))
                                   'NIL))
                       'NIL)
                 'NIL)
             (BINARY-APPEND ((LAMBDA (VAR-TYPE-DECLS)
                                     (IF VAR-TYPE-DECLS
                                         (CONS (CONS 'DECLARE VAR-TYPE-DECLS)
                                               'NIL)
                                         'NIL))
                             (GET-TYPE-DECLS (CAR (CAR BINDINGS))
                                             TYPE-DECLS))
                            (CONS REST 'NIL)))))
     (LET*-MACRO (CDR BINDINGS)
                 (REMOVE (CAR (CAR BINDINGS))
                         IGNORE-VARS)
                 (REMOVE (CAR (CAR BINDINGS))
                         IGNORABLE-VARS)
                 TYPE-DECLS BODY)
     TYPE-DECLS
     IGNORABLE-VARS IGNORE-VARS BINDINGS)))))

(DEFUN COLLECT-CDRS-WHEN-CAR-EQ (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQ X (CAR (CAR ALIST)))
               (BINARY-APPEND (CDR (CAR ALIST))
                              (COLLECT-CDRS-WHEN-CAR-EQ X (CDR ALIST)))
               (COLLECT-CDRS-WHEN-CAR-EQ X (CDR ALIST)))))

(DEFUN APPEND-LST (LST)
       (IF (ENDP LST)
           'NIL
           (BINARY-APPEND (CAR LST)
                          (APPEND-LST (CDR LST)))))

(DEFUN RESTRICT-ALIST (KEYS ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (MEMBER-EQ (CAR (CAR ALIST)) KEYS)
               (CONS (CAR ALIST)
                     (RESTRICT-ALIST KEYS (CDR ALIST)))
               (RESTRICT-ALIST KEYS (CDR ALIST)))))

(DEFUN
 FLOOR (I J)
 ((LAMBDA
   (Q)
   ((LAMBDA
     (N Q)
     ((LAMBDA
         (D N)
         (IF (= D '1)
             N
             (IF (NOT (< N '0))
                 (NONNEGATIVE-INTEGER-QUOTIENT N D)
                 (BINARY-+ (UNARY-- (NONNEGATIVE-INTEGER-QUOTIENT (UNARY-- N)
                                                                  D))
                           '-1))))
      (DENOMINATOR Q)
      N))
    (NUMERATOR Q)
    Q))
  (BINARY-* I (UNARY-/ J))))

(DEFUN
 CEILING (I J)
 ((LAMBDA
    (Q)
    ((LAMBDA
          (N Q)
          ((LAMBDA (D N)
                   (IF (= D '1)
                       N
                       (IF (NOT (< N '0))
                           (BINARY-+ (NONNEGATIVE-INTEGER-QUOTIENT N D)
                                     '1)
                           (UNARY-- (NONNEGATIVE-INTEGER-QUOTIENT (UNARY-- N)
                                                                  D)))))
           (DENOMINATOR Q)
           N))
     (NUMERATOR Q)
     Q))
  (BINARY-* I (UNARY-/ J))))

(DEFUN
 TRUNCATE (I J)
 ((LAMBDA
    (Q)
    ((LAMBDA
          (N Q)
          ((LAMBDA (D N)
                   (IF (= D '1)
                       N
                       (IF (NOT (< N '0))
                           (NONNEGATIVE-INTEGER-QUOTIENT N D)
                           (UNARY-- (NONNEGATIVE-INTEGER-QUOTIENT (UNARY-- N)
                                                                  D)))))
           (DENOMINATOR Q)
           N))
     (NUMERATOR Q)
     Q))
  (BINARY-* I (UNARY-/ J))))

(DEFUN
 ROUND (I J)
 ((LAMBDA
   (Q)
   (IF
      (INTEGERP Q)
      Q
      (IF (NOT (< Q '0))
          ((LAMBDA (FL Q)
                   ((LAMBDA (REMAINDER FL)
                            (IF (< '1/2 REMAINDER)
                                (BINARY-+ FL '1)
                                (IF (< REMAINDER '1/2)
                                    FL
                                    (IF (INTEGERP (BINARY-* FL (UNARY-/ '2)))
                                        FL (BINARY-+ FL '1)))))
                    (BINARY-+ Q (UNARY-- FL))
                    FL))
           (FLOOR Q '1)
           Q)
          ((LAMBDA (CL Q)
                   ((LAMBDA (REMAINDER CL)
                            (IF (< '-1/2 REMAINDER)
                                CL
                                (IF (< REMAINDER '-1/2)
                                    (BINARY-+ CL '-1)
                                    (IF (INTEGERP (BINARY-* CL (UNARY-/ '2)))
                                        CL (BINARY-+ CL '-1)))))
                    (BINARY-+ Q (UNARY-- CL))
                    CL))
           (CEILING Q '1)
           Q))))
  (BINARY-* I (UNARY-/ J))))

(DEFUN MOD (X Y) (BINARY-+ X (UNARY-- (BINARY-* (FLOOR X Y) Y))))

(DEFUN REM (X Y) (BINARY-+ X (UNARY-- (BINARY-* (TRUNCATE X Y) Y))))

(DEFUN EVENP (X) (INTEGERP (BINARY-* X (UNARY-/ '2))))

(DEFUN ODDP (X) (NOT (EVENP X)))

(DEFUN ZEROP (X) (EQL X '0))

(DEFUN PLUSP (X) (< '0 X))

(DEFUN MINUSP (X) (< X '0))

(DEFUN MIN (X Y) (IF (< X Y) X Y))

(DEFUN MAX (X Y) (IF (< Y X) X Y))

(DEFUN ABS (X) (IF (MINUSP X) (UNARY-- X) X))

(DEFUN SIGNUM (X) (IF (ZEROP X) '0 (IF (MINUSP X) '-1 '1)))

(DEFUN LOGNOT (I) (BINARY-+ (UNARY-- (IFIX I)) '-1))

(DEFTHM STANDARD-CHAR-P-NTH
        (IMPLIES (IF (STANDARD-CHAR-LISTP CHARS)
                     (IF (NOT (< I '0))
                         (< I (LEN CHARS))
                         'NIL)
                     'NIL)
                 (STANDARD-CHAR-P (NTH I CHARS))))

(DEFUN EXPT (R I)
       (IF (ZIP I)
           '1
           (IF (= (FIX R) '0)
               '0
               (IF (< '0 I)
                   (BINARY-* R (EXPT R (BINARY-+ I '-1)))
                   (BINARY-* (UNARY-/ R)
                             (EXPT R (BINARY-+ I '1)))))))

(DEFUN
    LOGCOUNT (X)
    (IF (ZIP X)
        '0
        (IF (< X '0)
            (LOGCOUNT (LOGNOT X))
            (IF (EVENP X)
                (LOGCOUNT (NONNEGATIVE-INTEGER-QUOTIENT X '2))
                (BINARY-+ '1
                          (LOGCOUNT (NONNEGATIVE-INTEGER-QUOTIENT X '2)))))))

(DEFUN NTHCDR (N L) (IF (ZP N) L (NTHCDR (BINARY-+ N '-1) (CDR L))))

(DEFUN LOGBITP (I J) (ODDP (FLOOR (IFIX J) (EXPT '2 (NFIX I)))))

(DEFUN ASH (I C) (FLOOR (BINARY-* (IFIX I) (EXPT '2 C)) '1))

(DEFTHM EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE
        (IMPLIES (IF (ACL2-NUMBERP R)
                     (NOT (EQUAL R '0))
                     'NIL)
                 (NOT (EQUAL (EXPT R I) '0))))

(DEFTHM RATIONALP-EXPT-TYPE-PRESCRIPTION
        (IMPLIES (RATIONALP R)
                 (RATIONALP (EXPT R I))))

(DEFAXIOM CHAR-CODE-LINEAR (< (CHAR-CODE X) '256))

(DEFAXIOM CODE-CHAR-TYPE (CHARACTERP (CODE-CHAR N)))

(DEFAXIOM CODE-CHAR-CHAR-CODE-IS-IDENTITY
          (IMPLIES (FORCE (CHARACTERP C))
                   (EQUAL (CODE-CHAR (CHAR-CODE C)) C)))

(DEFAXIOM CHAR-CODE-CODE-CHAR-IS-IDENTITY
          (IMPLIES (IF (FORCE (INTEGERP N))
                       (IF (FORCE (NOT (< N '0)))
                           (FORCE (< N '256))
                           'NIL)
                       'NIL)
                   (EQUAL (CHAR-CODE (CODE-CHAR N)) N)))

(DEFUN CHAR< (X Y) (< (CHAR-CODE X) (CHAR-CODE Y)))

(DEFUN CHAR> (X Y) (< (CHAR-CODE Y) (CHAR-CODE X)))

(DEFUN CHAR<= (X Y) (NOT (< (CHAR-CODE Y) (CHAR-CODE X))))

(DEFUN CHAR>= (X Y) (NOT (< (CHAR-CODE X) (CHAR-CODE Y))))

(DEFUN STRING<-L (L1 L2 I)
       (IF (ENDP L1)
           (IF (ENDP L2) 'NIL I)
           (IF (ENDP L2)
               'NIL
               (IF (EQL (CAR L1) (CAR L2))
                   (STRING<-L (CDR L1)
                              (CDR L2)
                              (BINARY-+ I '1))
                   (IF (CHAR< (CAR L1) (CAR L2))
                       I 'NIL)))))

(DEFUN STRING< (STR1 STR2)
       (STRING<-L (COERCE STR1 'LIST)
                  (COERCE STR2 'LIST)
                  '0))

(DEFUN STRING> (STR1 STR2) (STRING< STR2 STR1))

(DEFUN STRING<= (STR1 STR2)
       (IF (EQUAL STR1 STR2)
           (LENGTH STR1)
           (STRING< STR1 STR2)))

(DEFUN STRING>= (STR1 STR2)
       (IF (EQUAL STR1 STR2)
           (LENGTH STR1)
           (STRING> STR1 STR2)))

(DEFUN SYMBOL-< (X Y)
       ((LAMBDA (X1 Y1 Y X)
                (IF (STRING< X1 Y1)
                    (STRING< X1 Y1)
                    (IF (EQUAL X1 Y1)
                        (STRING< (SYMBOL-PACKAGE-NAME X)
                                 (SYMBOL-PACKAGE-NAME Y))
                        'NIL)))
        (SYMBOL-NAME X)
        (SYMBOL-NAME Y)
        Y X))

(DEFTHM STRING<-L-IRREFLEXIVE (NOT (STRING<-L X X I)))

(DEFTHM STRING<-IRREFLEXIVE (NOT (STRING< S S)))

(DEFUN SUBSTITUTE-AC (NEW OLD SEQ ACC)
       (IF (ENDP SEQ)
           (REVERSE ACC)
           (IF (EQL OLD (CAR SEQ))
               (SUBSTITUTE-AC NEW OLD (CDR SEQ)
                              (CONS NEW ACC))
               (SUBSTITUTE-AC NEW OLD (CDR SEQ)
                              (CONS (CAR SEQ) ACC)))))

(DEFUN SUBSTITUTE (NEW OLD SEQ)
       (IF (STRINGP SEQ)
           (COERCE (SUBSTITUTE-AC NEW OLD (COERCE SEQ 'LIST)
                                  'NIL)
                   'STRING)
           (SUBSTITUTE-AC NEW OLD SEQ 'NIL)))

(DEFUN SUBSETP (X Y)
       (IF (ENDP X)
           'T
           (IF (MEMBER (CAR X) Y)
               (SUBSETP (CDR X) Y)
               'NIL)))

(DEFUN SUBLIS (ALIST TREE)
       (IF (ATOM TREE)
           ((LAMBDA (PAIR TREE)
                    (IF PAIR (CDR PAIR) TREE))
            (ASSOC TREE ALIST)
            TREE)
           (CONS (SUBLIS ALIST (CAR TREE))
                 (SUBLIS ALIST (CDR TREE)))))

(DEFUN SUBST (NEW OLD TREE)
       (IF (EQL OLD TREE)
           NEW
           (IF (ATOM TREE)
               TREE
               (CONS (SUBST NEW OLD (CAR TREE))
                     (SUBST NEW OLD (CDR TREE))))))

(DEFUN WORLDP (ALIST)
       (IF (ATOM ALIST)
           (EQ ALIST 'NIL)
           (IF (CONSP (CAR ALIST))
               (IF (SYMBOLP (CAR (CAR ALIST)))
                   (IF (CONSP (CDR (CAR ALIST)))
                       (IF (SYMBOLP (CAR (CDR (CAR ALIST))))
                           (WORLDP (CDR ALIST))
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)))

(DEFTHM WORLDP-FORWARD-TO-ASSOC-EQ-EQUAL-ALISTP
        (IMPLIES (WORLDP X)
                 (ASSOC-EQ-EQUAL-ALISTP X)))

(DEFUN PUTPROP (SYMB KEY VALUE WORLD-ALIST)
       (CONS (CONS SYMB (CONS KEY VALUE))
             WORLD-ALIST))

(DEFUN
 GETPROP-DEFAULT (SYMB KEY DEFAULT)
 (PROG2$
  (IF
   (CONSP DEFAULT)
   (IF
    (EQ (CAR DEFAULT) ':ERROR)
    (IF
     (CONSP (CDR DEFAULT))
     (IF (STRINGP (CAR (CDR DEFAULT)))
         (IF (NULL (CDR (CDR DEFAULT)))
             (HARD-ERROR
                  'GETPROP
                  '"No property was found under symbol ~x0 for key ~x1.  ~@2"
                  (CONS (CONS '#\0 SYMB)
                        (CONS (CONS '#\1 KEY)
                              (CONS (CONS '#\2 (CAR (CDR DEFAULT)))
                                    'NIL))))
             'NIL)
         'NIL)
     'NIL)
    'NIL)
   'NIL)
  DEFAULT))

(DEFUN FGETPROP (SYMB KEY DEFAULT WORLD-ALIST)
       (IF (ENDP WORLD-ALIST)
           DEFAULT
           (IF (IF (EQ SYMB (CAR (CAR WORLD-ALIST)))
                   (EQ KEY (CAR (CDR (CAR WORLD-ALIST))))
                   'NIL)
               ((LAMBDA (ANS DEFAULT)
                        (IF (EQ ANS ':ACL2-PROPERTY-UNBOUND)
                            DEFAULT ANS))
                (CDR (CDR (CAR WORLD-ALIST)))
                DEFAULT)
               (FGETPROP SYMB KEY DEFAULT (CDR WORLD-ALIST)))))

(DEFUN SGETPROP
       (SYMB KEY DEFAULT WORLD-NAME WORLD-ALIST)
       (IF (ENDP WORLD-ALIST)
           DEFAULT
           (IF (IF (EQ SYMB (CAR (CAR WORLD-ALIST)))
                   (EQ KEY (CAR (CDR (CAR WORLD-ALIST))))
                   'NIL)
               ((LAMBDA (ANS DEFAULT)
                        (IF (EQ ANS ':ACL2-PROPERTY-UNBOUND)
                            DEFAULT ANS))
                (CDR (CDR (CAR WORLD-ALIST)))
                DEFAULT)
               (SGETPROP SYMB KEY
                         DEFAULT WORLD-NAME (CDR WORLD-ALIST)))))

(DEFUN ORDERED-SYMBOL-ALISTP (X)
       (IF (ATOM X)
           (NULL X)
           (IF (ATOM (CAR X))
               'NIL
               (IF (SYMBOLP (CAR (CAR X)))
                   (IF (IF (ATOM (CDR X))
                           (ATOM (CDR X))
                           (IF (CONSP (CAR (CDR X)))
                               (IF (SYMBOLP (CAR (CAR (CDR X))))
                                   (SYMBOL-< (CAR (CAR X))
                                             (CAR (CAR (CDR X))))
                                   'NIL)
                               'NIL))
                       (ORDERED-SYMBOL-ALISTP (CDR X))
                       'NIL)
                   'NIL))))

(DEFTHM ORDERED-SYMBOL-ALISTP-FORWARD-TO-SYMBOL-ALISTP
        (IMPLIES (ORDERED-SYMBOL-ALISTP X)
                 (SYMBOL-ALISTP X)))

(DEFUN ADD-PAIR (KEY VALUE L)
       (IF (ENDP L)
           (CONS (CONS KEY VALUE) 'NIL)
           (IF (EQ KEY (CAR (CAR L)))
               (CONS (CONS KEY VALUE) (CDR L))
               (IF (SYMBOL-< KEY (CAR (CAR L)))
                   (CONS (CONS KEY VALUE) L)
                   (CONS (CAR L)
                         (ADD-PAIR KEY VALUE (CDR L)))))))

(DEFUN REMOVE-FIRST-PAIR (KEY L)
       (IF (ENDP L)
           'NIL
           (IF (EQ KEY (CAR (CAR L)))
               (CDR L)
               (CONS (CAR L)
                     (REMOVE-FIRST-PAIR KEY (CDR L))))))

(DEFUN GETPROPS1 (ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (IF (NULL (CDR (CAR ALIST)))
                   (NULL (CDR (CAR ALIST)))
                   (EQ (CAR (CDR (CAR ALIST)))
                       ':ACL2-PROPERTY-UNBOUND))
               (GETPROPS1 (CDR ALIST))
               (CONS (CONS (CAR (CAR ALIST))
                           (CAR (CDR (CAR ALIST))))
                     (GETPROPS1 (CDR ALIST))))))

(DEFUN
    GETPROPS (SYMB WORLD-NAME WORLD-ALIST)
    (IF (ENDP WORLD-ALIST)
        'NIL
        (IF (EQ SYMB (CAR (CAR WORLD-ALIST)))
            ((LAMBDA (ALIST WORLD-ALIST)
                     (IF (EQ (CDR (CDR (CAR WORLD-ALIST)))
                             ':ACL2-PROPERTY-UNBOUND)
                         (IF (ASSOC-EQ (CAR (CDR (CAR WORLD-ALIST)))
                                       ALIST)
                             (REMOVE-FIRST-PAIR (CAR (CDR (CAR WORLD-ALIST)))
                                                ALIST)
                             ALIST)
                         (ADD-PAIR (CAR (CDR (CAR WORLD-ALIST)))
                                   (CDR (CDR (CAR WORLD-ALIST)))
                                   ALIST)))
             (GETPROPS SYMB WORLD-NAME (CDR WORLD-ALIST))
             WORLD-ALIST)
            (GETPROPS SYMB WORLD-NAME (CDR WORLD-ALIST)))))

(DEFTHM EQUAL-CHAR-CODE
        (IMPLIES (IF (CHARACTERP X) (CHARACTERP Y) 'NIL)
                 (IMPLIES (EQUAL (CHAR-CODE X) (CHAR-CODE Y))
                          (EQUAL X Y))))

(DEFUN HAS-PROPSP1
       (ALIST EXCEPTIONS KNOWN-UNBOUND)
       (IF (ENDP ALIST)
           'NIL
           (IF (IF (NULL (CDR (CAR ALIST)))
                   (NULL (CDR (CAR ALIST)))
                   (IF (EQ (CAR (CDR (CAR ALIST)))
                           ':ACL2-PROPERTY-UNBOUND)
                       (EQ (CAR (CDR (CAR ALIST)))
                           ':ACL2-PROPERTY-UNBOUND)
                       (IF (MEMBER-EQ (CAR (CAR ALIST)) EXCEPTIONS)
                           (MEMBER-EQ (CAR (CAR ALIST)) EXCEPTIONS)
                           (MEMBER-EQ (CAR (CAR ALIST))
                                      KNOWN-UNBOUND))))
               (HAS-PROPSP1 (CDR ALIST)
                            EXCEPTIONS KNOWN-UNBOUND)
               'T)))

(DEFUN HAS-PROPSP
       (SYMB EXCEPTIONS
             WORLD-NAME WORLD-ALIST KNOWN-UNBOUND)
       (IF (ENDP WORLD-ALIST)
           'NIL
           (IF (IF (NOT (EQ SYMB (CAR (CAR WORLD-ALIST))))
                   (NOT (EQ SYMB (CAR (CAR WORLD-ALIST))))
                   (IF (MEMBER-EQ (CAR (CDR (CAR WORLD-ALIST)))
                                  EXCEPTIONS)
                       (MEMBER-EQ (CAR (CDR (CAR WORLD-ALIST)))
                                  EXCEPTIONS)
                       (MEMBER-EQ (CAR (CDR (CAR WORLD-ALIST)))
                                  KNOWN-UNBOUND)))
               (HAS-PROPSP SYMB
                           EXCEPTIONS WORLD-NAME (CDR WORLD-ALIST)
                           KNOWN-UNBOUND)
               (IF (EQ (CDR (CDR (CAR WORLD-ALIST)))
                       ':ACL2-PROPERTY-UNBOUND)
                   (HAS-PROPSP SYMB
                               EXCEPTIONS WORLD-NAME (CDR WORLD-ALIST)
                               (CONS (CAR (CDR (CAR WORLD-ALIST)))
                                     KNOWN-UNBOUND))
                   'T))))

(DEFUN EXTEND-WORLD (NAME WRLD) WRLD)

(DEFUN RETRACT-WORLD (NAME WRLD) WRLD)

(DEFUN
 GLOBAL-VAL (VAR WRLD)
 (FGETPROP
  VAR 'GLOBAL-VALUE
  '(:ERROR
    "GLOBAL-VAL didn't find a value.  Initialize this ~
                     symbol in PRIMORDIAL-WORLD-GLOBALS.")
  WRLD))

(DEFUN FUNCTION-SYMBOLP (SYM WRLD)
       (NOT (EQ (FGETPROP SYM 'FORMALS 'T WRLD)
                'T)))

(DEFUN WEAK-SATISFIES-TYPE-SPEC-P (X)
       (IF (CONSP X)
           (IF (EQ (CAR X) 'SATISFIES)
               (IF (TRUE-LISTP X)
                   (IF (EQUAL (LENGTH X) '2)
                       (SYMBOLP (CAR (CDR X)))
                       'NIL)
                   'NIL)
               'NIL)
           'NIL))

(DEFUN THE-ERROR (X Y) (CDR (CONS X Y)))

(DEFUN SET-DIFFERENCE-EQUAL (L1 L2)
       (IF (ENDP L1)
           'NIL
           (IF (MEMBER-EQUAL (CAR L1) L2)
               (SET-DIFFERENCE-EQUAL (CDR L1) L2)
               (CONS (CAR L1)
                     (SET-DIFFERENCE-EQUAL (CDR L1) L2)))))

(DEFUN BOUNDED-INTEGER-ALISTP (L N)
       (IF (ATOM L)
           (NULL L)
           (IF (CONSP (CAR L))
               ((LAMBDA (KEY L N)
                        (IF (IF (EQ KEY ':HEADER)
                                (EQ KEY ':HEADER)
                                (IF (INTEGERP KEY)
                                    (IF (INTEGERP N)
                                        (IF (NOT (< KEY '0)) (< KEY N) 'NIL)
                                        'NIL)
                                    'NIL))
                            (BOUNDED-INTEGER-ALISTP (CDR L) N)
                            'NIL))
                (CAR (CAR L))
                L N)
               'NIL)))

(DEFTHM BOUNDED-INTEGER-ALISTP-FORWARD-TO-EQLABLE-ALISTP
        (IMPLIES (BOUNDED-INTEGER-ALISTP X N)
                 (EQLABLE-ALISTP X)))

(DEFUN KEYWORD-VALUE-LISTP (L)
       (IF (ATOM L)
           (NULL L)
           (IF (KEYWORDP (CAR L))
               (IF (CONSP (CDR L))
                   (KEYWORD-VALUE-LISTP (CDR (CDR L)))
                   'NIL)
               'NIL)))

(DEFTHM KEYWORD-VALUE-LISTP-FORWARD-TO-TRUE-LISTP
        (IMPLIES (KEYWORD-VALUE-LISTP X)
                 (TRUE-LISTP X)))

(DEFUN ASSOC-KEYWORD (KEY L)
       (IF (ENDP L)
           'NIL
           (IF (EQ KEY (CAR L))
               L (ASSOC-KEYWORD KEY (CDR (CDR L))))))

(DEFTHM KEYWORD-VALUE-LISTP-ASSOC-KEYWORD
        (IMPLIES (KEYWORD-VALUE-LISTP L)
                 (KEYWORD-VALUE-LISTP (ASSOC-KEYWORD KEY L))))

(DEFTHM CONSP-ASSOC-EQ
        (IMPLIES (ALISTP L)
                 (IF (CONSP (ASSOC-EQ NAME L))
                     (CONSP (ASSOC-EQ NAME L))
                     (EQUAL (ASSOC-EQ NAME L) 'NIL))))

(DEFUN
 ARRAY1P (NAME L)
 (IF
  (SYMBOLP NAME)
  (IF
   (ALISTP L)
   ((LAMBDA
     (HEADER-KEYWORD-LIST L)
     (IF
      (KEYWORD-VALUE-LISTP HEADER-KEYWORD-LIST)
      ((LAMBDA
        (DIMENSIONS MAXIMUM-LENGTH L)
        (IF
          (TRUE-LISTP DIMENSIONS)
          (IF (EQUAL (LENGTH DIMENSIONS) '1)
              (IF (INTEGERP (CAR DIMENSIONS))
                  (IF (INTEGERP MAXIMUM-LENGTH)
                      (IF (< '0 (CAR DIMENSIONS))
                          (IF (< (CAR DIMENSIONS) MAXIMUM-LENGTH)
                              (IF (NOT (< '2147483647 MAXIMUM-LENGTH))
                                  (BOUNDED-INTEGER-ALISTP L (CAR DIMENSIONS))
                                  'NIL)
                              'NIL)
                          'NIL)
                      'NIL)
                  'NIL)
              'NIL)
          'NIL))
       (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                HEADER-KEYWORD-LIST)))
       (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                HEADER-KEYWORD-LIST)))
       L)
      'NIL))
    (CDR (ASSOC-EQ ':HEADER L))
    L)
   'NIL)
  'NIL))

(DEFTHM
 ARRAY1P-FORWARD
 (IMPLIES
  (ARRAY1P NAME L)
  (IF
   (SYMBOLP NAME)
   (IF
    (ALISTP L)
    (IF
     (KEYWORD-VALUE-LISTP (CDR (ASSOC-EQ ':HEADER L)))
     (IF
      (TRUE-LISTP (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                           (CDR (ASSOC-EQ ':HEADER L))))))
      (IF
       (EQUAL
            (LENGTH (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                             (CDR (ASSOC-EQ ':HEADER L))))))
            '1)
       (IF
        (INTEGERP
             (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                           (CDR (ASSOC-EQ ':HEADER L)))))))
        (IF
         (INTEGERP (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                            (CDR (ASSOC-EQ ':HEADER L))))))
         (IF
          (< '0
             (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                           (CDR (ASSOC-EQ ':HEADER L)))))))
          (IF
           (< (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                            (CDR (ASSOC-EQ ':HEADER L))))))
              (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                       (CDR (ASSOC-EQ ':HEADER L))))))
           (IF
            (NOT (< '2147483647
                    (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                             (CDR (ASSOC-EQ ':HEADER L)))))))
            (BOUNDED-INTEGER-ALISTP
               L
               (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                             (CDR (ASSOC-EQ ':HEADER L)))))))
            'NIL)
           'NIL)
          'NIL)
         'NIL)
        'NIL)
       'NIL)
      'NIL)
     'NIL)
    'NIL)
   'NIL)))

(DEFTHM
 ARRAY1P-LINEAR
 (IMPLIES
    (ARRAY1P NAME L)
    (IF (< '0
           (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                         (CDR (ASSOC-EQ ':HEADER L)))))))
        (IF (< (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                             (CDR (ASSOC-EQ ':HEADER L))))))
               (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                        (CDR (ASSOC-EQ ':HEADER L))))))
            (NOT (< '2147483647
                    (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                             (CDR (ASSOC-EQ ':HEADER L)))))))
            'NIL)
        'NIL)))

(DEFUN
 BOUNDED-INTEGER-ALISTP2 (L I J)
 (IF
  (ATOM L)
  (NULL L)
  (IF
   (CONSP (CAR L))
   (IF
    ((LAMBDA
      (KEY I J)
      (IF
       (EQ KEY ':HEADER)
       (EQ KEY ':HEADER)
       (IF
          (CONSP KEY)
          ((LAMBDA (I1 J1 J I)
                   (IF (INTEGERP I1)
                       (IF (INTEGERP J1)
                           (IF (INTEGERP I)
                               (IF (INTEGERP J)
                                   (IF (NOT (< I1 '0))
                                       (IF (< I1 I)
                                           (IF (NOT (< J1 '0)) (< J1 J) 'NIL)
                                           'NIL)
                                       'NIL)
                                   'NIL)
                               'NIL)
                           'NIL)
                       'NIL))
           (CAR KEY)
           (CDR KEY)
           J I)
          'NIL)))
     (CAR (CAR L))
     I J)
    (BOUNDED-INTEGER-ALISTP2 (CDR L) I J)
    'NIL)
   'NIL)))

(DEFUN ASSOC2 (I J L)
       (IF (ATOM L)
           'NIL
           (IF (IF (CONSP (CAR L))
                   (IF (CONSP (CAR (CAR L)))
                       (IF (EQL I (CAR (CAR (CAR L))))
                           (EQL J (CDR (CAR (CAR L))))
                           'NIL)
                       'NIL)
                   'NIL)
               (CAR L)
               (ASSOC2 I J (CDR L)))))

(DEFUN
 ARRAY2P (NAME L)
 (IF
  (SYMBOLP NAME)
  (IF
   (ALISTP L)
   ((LAMBDA
     (HEADER-KEYWORD-LIST L)
     (IF
      (KEYWORD-VALUE-LISTP HEADER-KEYWORD-LIST)
      ((LAMBDA
        (DIMENSIONS MAXIMUM-LENGTH L)
        (IF
         (TRUE-LISTP DIMENSIONS)
         (IF
          (EQUAL (LENGTH DIMENSIONS) '2)
          ((LAMBDA
             (D1 D2 L MAXIMUM-LENGTH)
             (IF (INTEGERP D1)
                 (IF (INTEGERP D2)
                     (IF (INTEGERP MAXIMUM-LENGTH)
                         (IF (< '0 D1)
                             (IF (< '0 D2)
                                 (IF (< (BINARY-* D1 D2) MAXIMUM-LENGTH)
                                     (IF (NOT (< '2147483647 MAXIMUM-LENGTH))
                                         (BOUNDED-INTEGER-ALISTP2 L D1 D2)
                                         'NIL)
                                     'NIL)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 'NIL))
           (CAR DIMENSIONS)
           (CAR (CDR DIMENSIONS))
           L MAXIMUM-LENGTH)
          'NIL)
         'NIL))
       (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                HEADER-KEYWORD-LIST)))
       (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                HEADER-KEYWORD-LIST)))
       L)
      'NIL))
    (CDR (ASSOC-EQ ':HEADER L))
    L)
   'NIL)
  'NIL))

(DEFTHM
 ARRAY2P-FORWARD
 (IMPLIES
  (ARRAY2P NAME L)
  (IF
   (SYMBOLP NAME)
   (IF
    (ALISTP L)
    (IF
     (KEYWORD-VALUE-LISTP (CDR (ASSOC-EQ ':HEADER L)))
     (IF
      (TRUE-LISTP (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                           (CDR (ASSOC-EQ ':HEADER L))))))
      (IF
       (EQUAL
            (LENGTH (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                             (CDR (ASSOC-EQ ':HEADER L))))))
            '2)
       (IF
        (INTEGERP
             (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                           (CDR (ASSOC-EQ ':HEADER L)))))))
        (IF
         (INTEGERP
          (CAR
              (CDR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                            (CDR (ASSOC-EQ ':HEADER L))))))))
         (IF
          (INTEGERP (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                             (CDR (ASSOC-EQ ':HEADER L))))))
          (IF
           (< '0
              (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                            (CDR (ASSOC-EQ ':HEADER L)))))))
           (IF
            (<
             '0
             (CAR
              (CDR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                            (CDR (ASSOC-EQ ':HEADER L))))))))
            (IF
             (<
              (BINARY-*
               (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                             (CDR (ASSOC-EQ ':HEADER L))))))
               (CAR
                (CDR
                   (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                            (CDR (ASSOC-EQ ':HEADER L))))))))
              (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                       (CDR (ASSOC-EQ ':HEADER L))))))
             (IF
              (NOT
                 (< '2147483647
                    (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                             (CDR (ASSOC-EQ ':HEADER L)))))))
              (BOUNDED-INTEGER-ALISTP2
               L
               (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                             (CDR (ASSOC-EQ ':HEADER L))))))
               (CAR
                (CDR
                   (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                            (CDR (ASSOC-EQ ':HEADER L))))))))
              'NIL)
             'NIL)
            'NIL)
           'NIL)
          'NIL)
         'NIL)
        'NIL)
       'NIL)
      'NIL)
     'NIL)
    'NIL)
   'NIL)))

(DEFTHM
 ARRAY2P-LINEAR
 (IMPLIES
  (ARRAY2P NAME L)
  (IF
   (< '0
      (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                    (CDR (ASSOC-EQ ':HEADER L)))))))
   (IF
    (< '0
       (CAR (CDR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                          (CDR (ASSOC-EQ ':HEADER L))))))))
    (IF
     (<
      (BINARY-*
         (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                       (CDR (ASSOC-EQ ':HEADER L))))))
         (CAR (CDR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                            (CDR (ASSOC-EQ ':HEADER L))))))))
      (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                               (CDR (ASSOC-EQ ':HEADER L))))))
     (NOT (< '2147483647
             (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                      (CDR (ASSOC-EQ ':HEADER L)))))))
     'NIL)
    'NIL)
   'NIL)))

(DEFUN HEADER (NAME L) (PROG2$ NAME (ASSOC-EQ ':HEADER L)))

(DEFUN DIMENSIONS (NAME L)
       (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                (CDR (HEADER NAME L))))))

(DEFUN MAXIMUM-LENGTH (NAME L)
       (CAR (CDR (ASSOC-KEYWORD ':MAXIMUM-LENGTH
                                (CDR (HEADER NAME L))))))

(DEFUN DEFAULT (NAME L)
       (CAR (CDR (ASSOC-KEYWORD ':DEFAULT
                                (CDR (HEADER NAME L))))))

(DEFTHM CONSP-ASSOC
        (IMPLIES (ALISTP L)
                 (IF (CONSP (ASSOC NAME L))
                     (CONSP (ASSOC NAME L))
                     (EQUAL (ASSOC NAME L) 'NIL))))

(DEFUN AREF1 (NAME L N)
       ((LAMBDA (X L NAME)
                (IF (NULL X) (DEFAULT NAME L) (CDR X)))
        (IF (NOT (EQ N ':HEADER))
            (ASSOC N L)
            'NIL)
        L NAME))

(DEFUN COMPRESS11 (NAME L I N DEFAULT)
       (IF (ZP (BINARY-+ N (UNARY-- I)))
           'NIL
           ((LAMBDA (PAIR N I L NAME DEFAULT)
                    (IF (IF (NULL PAIR)
                            (NULL PAIR)
                            (EQUAL (CDR PAIR) DEFAULT))
                        (COMPRESS11 NAME L (BINARY-+ I '1)
                                    N DEFAULT)
                        (CONS PAIR
                              (COMPRESS11 NAME L (BINARY-+ I '1)
                                          N DEFAULT))))
            (ASSOC I L)
            N I L NAME DEFAULT)))

(DEFUN ARRAY-ORDER (HEADER)
       ((LAMBDA (ORDERP)
                (IF (IF ORDERP
                        (IF (EQ (CAR (CDR ORDERP)) 'NIL)
                            (EQ (CAR (CDR ORDERP)) 'NIL)
                            (EQ (CAR (CDR ORDERP)) ':NONE))
                        'NIL)
                    'NIL
                    (IF (IF ORDERP (EQ (CAR (CDR ORDERP)) '>)
                            'NIL)
                        '>
                        '<)))
        (ASSOC-KEYWORD ':ORDER (CDR HEADER))))

(DEFUN
 COMPRESS1 (NAME L)
 ((LAMBDA
   (CASE-DO-NOT-USE-ELSEWHERE L NAME)
   (IF
    (EQL CASE-DO-NOT-USE-ELSEWHERE '<)
    (CONS (HEADER NAME L)
          (COMPRESS11 NAME L '0
                      (CAR (DIMENSIONS NAME L))
                      (DEFAULT NAME L)))
    (IF
     (EQL CASE-DO-NOT-USE-ELSEWHERE '>)
     (CONS (HEADER NAME L)
           (REVERSE (COMPRESS11 NAME L '0
                                (CAR (DIMENSIONS NAME L))
                                (DEFAULT NAME L))))
     (PROG2$
      (IF
       (< (MAXIMUM-LENGTH NAME L) (LENGTH L))
       (HARD-ERROR
        'COMPRESS1
        '"Attempted to compress a one-dimensional array named ~
                        ~x0 whose header specifies :ORDER ~x1 and whose ~
                        length, ~x2, exceeds its maximum-length, ~x3."
        (CONS (CONS '#\0 NAME)
              (CONS (CONS '#\1 'NIL)
                    (CONS (CONS '#\2 (LENGTH L))
                          (CONS (CONS '#\3 (MAXIMUM-LENGTH NAME L))
                                'NIL)))))
       'NIL)
      L))))
  (ARRAY-ORDER (HEADER NAME L))
  L NAME))

(DEFTHM
   ARRAY1P-CONS
   (IMPLIES
        (IF (< N
               (CAR (CAR (CDR (ASSOC-KEYWORD ':DIMENSIONS
                                             (CDR (ASSOC-EQ ':HEADER L)))))))
            (IF (NOT (< N '0))
                (IF (INTEGERP N) (ARRAY1P NAME L) 'NIL)
                'NIL)
            'NIL)
        (ARRAY1P NAME (CONS (CONS N VAL) L))))

(DEFUN ASET1 (NAME L N VAL)
       ((LAMBDA (L NAME)
                (IF (< (MAXIMUM-LENGTH NAME L) (LENGTH L))
                    (COMPRESS1 NAME L)
                    L))
        (CONS (CONS N VAL) L)
        NAME))

(DEFUN AREF2 (NAME L I J)
       ((LAMBDA (X L NAME)
                (IF (NULL X) (DEFAULT NAME L) (CDR X)))
        (ASSOC2 I J L)
        L NAME))

(DEFUN COMPRESS211 (NAME L I X J DEFAULT)
       (IF (ZP (BINARY-+ J (UNARY-- X)))
           'NIL
           ((LAMBDA (PAIR J X I L NAME DEFAULT)
                    (IF (IF (NULL PAIR)
                            (NULL PAIR)
                            (EQUAL (CDR PAIR) DEFAULT))
                        (COMPRESS211 NAME L I (BINARY-+ '1 X)
                                     J DEFAULT)
                        (CONS PAIR
                              (COMPRESS211 NAME L I (BINARY-+ '1 X)
                                           J DEFAULT))))
            (ASSOC2 I X L)
            J X I L NAME DEFAULT)))

(DEFUN COMPRESS21 (NAME L N I J DEFAULT)
       (IF (ZP (BINARY-+ I (UNARY-- N)))
           'NIL
           (BINARY-APPEND (COMPRESS211 NAME L N '0 J DEFAULT)
                          (COMPRESS21 NAME L (BINARY-+ N '1)
                                      I J DEFAULT))))

(DEFUN COMPRESS2 (NAME L)
       (CONS (HEADER NAME L)
             (COMPRESS21 NAME L '0
                         (CAR (DIMENSIONS NAME L))
                         (CAR (CDR (DIMENSIONS NAME L)))
                         (DEFAULT NAME L))))

(DEFTHM ARRAY2P-CONS
        (IMPLIES (IF (< J (CAR (CDR (DIMENSIONS NAME L))))
                     (IF (NOT (< J '0))
                         (IF (INTEGERP J)
                             (IF (< I (CAR (DIMENSIONS NAME L)))
                                 (IF (NOT (< I '0))
                                     (IF (INTEGERP I) (ARRAY2P NAME L) 'NIL)
                                     'NIL)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 (ARRAY2P NAME (CONS (CONS (CONS I J) VAL) L))))

(DEFUN ASET2 (NAME L I J VAL)
       ((LAMBDA (L NAME)
                (IF (< (MAXIMUM-LENGTH NAME L) (LENGTH L))
                    (COMPRESS2 NAME L)
                    L))
        (CONS (CONS (CONS I J) VAL) L)
        NAME))

(DEFUN FLUSH-COMPRESS (NAME) 'NIL)

(DEFUN CDRN (X I)
       (IF (ZP I)
           X
           (CDRN (CONS 'CDR (CONS X 'NIL))
                 (BINARY-+ '-1 I))))

(DEFUN MV-NTH (N L)
       (IF (ENDP L)
           'NIL
           (IF (ZP N)
               (CAR L)
               (MV-NTH (BINARY-+ '-1 N) (CDR L)))))

(DEFUN MAKE-MV-NTHS (ARGS CALL I)
       (IF (ENDP ARGS)
           'NIL
           (CONS (CONS (CAR ARGS)
                       (CONS (CONS 'MV-NTH (CONS I (CONS CALL 'NIL)))
                             'NIL))
                 (MAKE-MV-NTHS (CDR ARGS)
                               CALL (BINARY-+ I '1)))))

(DEFUN UPDATE-NTH (KEY VAL L)
       (IF (ZP KEY)
           (CONS VAL (CDR L))
           (CONS (CAR L)
                 (UPDATE-NTH (BINARY-+ '-1 KEY)
                             VAL (CDR L)))))

(DEFUN UPDATE-NTH-ARRAY (J KEY VAL L)
       (UPDATE-NTH J (UPDATE-NTH KEY VAL (NTH J L))
                   L))

(DEFUN 32-BIT-INTEGERP (X)
       (IF (INTEGERP X)
           (IF (NOT (< '2147483647 X))
               (NOT (< X '-2147483648))
               'NIL)
           'NIL))

(DEFTHM 32-BIT-INTEGERP-FORWARD-TO-INTEGERP
        (IMPLIES (32-BIT-INTEGERP X)
                 (INTEGERP X)))

(DEFUN RATIONAL-LISTP (L)
       (IF (ATOM L)
           (EQ L 'NIL)
           (IF (RATIONALP (CAR L))
               (RATIONAL-LISTP (CDR L))
               'NIL)))

(DEFTHM RATIONAL-LISTP-FORWARD-TO-TRUE-LISTP
        (IMPLIES (RATIONAL-LISTP X)
                 (TRUE-LISTP X)))

(DEFUN INTEGER-LISTP (L)
       (IF (ATOM L)
           (EQUAL L 'NIL)
           (IF (INTEGERP (CAR L))
               (INTEGER-LISTP (CDR L))
               'NIL)))

(DEFTHM INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP
        (IMPLIES (INTEGER-LISTP X)
                 (RATIONAL-LISTP X)))

(DEFUN 32-BIT-INTEGER-LISTP (L)
       (IF (ATOM L)
           (EQUAL L 'NIL)
           (IF (32-BIT-INTEGERP (CAR L))
               (32-BIT-INTEGER-LISTP (CDR L))
               'NIL)))

(DEFTHM 32-BIT-INTEGER-LISTP-FORWARD-TO-INTEGER-LISTP
        (IMPLIES (32-BIT-INTEGER-LISTP X)
                 (INTEGER-LISTP X)))

(DEFUN OPEN-INPUT-CHANNELS (ST) (NTH '0 ST))

(DEFUN UPDATE-OPEN-INPUT-CHANNELS (X ST) (UPDATE-NTH '0 X ST))

(DEFUN OPEN-OUTPUT-CHANNELS (ST) (NTH '1 ST))

(DEFUN UPDATE-OPEN-OUTPUT-CHANNELS (X ST) (UPDATE-NTH '1 X ST))

(DEFUN GLOBAL-TABLE (ST) (NTH '2 ST))

(DEFUN UPDATE-GLOBAL-TABLE (X ST) (UPDATE-NTH '2 X ST))

(DEFUN T-STACK (ST) (NTH '3 ST))

(DEFUN UPDATE-T-STACK (X ST) (UPDATE-NTH '3 X ST))

(DEFUN 32-BIT-INTEGER-STACK (ST) (NTH '4 ST))

(DEFUN UPDATE-32-BIT-INTEGER-STACK (X ST) (UPDATE-NTH '4 X ST))

(DEFUN BIG-CLOCK-ENTRY (ST) (NTH '5 ST))

(DEFUN UPDATE-BIG-CLOCK-ENTRY (X ST) (UPDATE-NTH '5 X ST))

(DEFUN IDATES (ST) (NTH '6 ST))

(DEFUN UPDATE-IDATES (X ST) (UPDATE-NTH '6 X ST))

(DEFUN ACL2-ORACLE (ST) (NTH '7 ST))

(DEFUN UPDATE-ACL2-ORACLE (X ST) (UPDATE-NTH '7 X ST))

(DEFUN FILE-CLOCK (ST) (NTH '8 ST))

(DEFUN UPDATE-FILE-CLOCK (X ST) (UPDATE-NTH '8 X ST))

(DEFUN READABLE-FILES (ST) (NTH '9 ST))

(DEFUN WRITTEN-FILES (ST) (NTH '10 ST))

(DEFUN UPDATE-WRITTEN-FILES (X ST) (UPDATE-NTH '10 X ST))

(DEFUN READ-FILES (ST) (NTH '11 ST))

(DEFUN UPDATE-READ-FILES (X ST) (UPDATE-NTH '11 X ST))

(DEFUN WRITEABLE-FILES (ST) (NTH '12 ST))

(DEFUN LIST-ALL-PACKAGE-NAMES-LST (ST) (NTH '13 ST))

(DEFUN UPDATE-LIST-ALL-PACKAGE-NAMES-LST (X ST) (UPDATE-NTH '13 X ST))

(DEFUN USER-STOBJ-ALIST1 (ST) (NTH '14 ST))

(DEFUN UPDATE-USER-STOBJ-ALIST1 (X ST) (UPDATE-NTH '14 X ST))

(DEFUN
 INIT-IPRINT-AR (HARD-BOUND ENABLEDP)
 ((LAMBDA
   (DIM ENABLEDP)
   (CONS
    (CONS
     ':HEADER
     (CONS
      ':DIMENSIONS
      (CONS
       (CONS DIM 'NIL)
       (CONS ':MAXIMUM-LENGTH
             (CONS (BINARY-* '4 DIM)
                   (CONS ':DEFAULT
                         (CONS 'NIL
                               (CONS ':NAME
                                     (CONS 'IPRINT-AR
                                           (CONS ':ORDER
                                                 (CONS ':NONE 'NIL)))))))))))
    (CONS (CONS '0
                (IF ENABLEDP '0 (CONS '0 'NIL)))
          'NIL)))
  (BINARY-+ '1 HARD-BOUND)
  ENABLEDP))

(DEFUN ALL-BOUNDP (ALIST1 ALIST2)
       (IF (ENDP ALIST1)
           'T
           (IF (ASSOC (CAR (CAR ALIST1)) ALIST2)
               (ALL-BOUNDP (CDR ALIST1) ALIST2)
               'NIL)))

(DEFUN KNOWN-PACKAGE-ALISTP (X)
       (IF (ATOM X)
           (NULL X)
           (IF (TRUE-LISTP (CAR X))
               (IF (STRINGP (CAR (CAR X)))
                   (IF (SYMBOL-LISTP (CAR (CDR (CAR X))))
                       (KNOWN-PACKAGE-ALISTP (CDR X))
                       'NIL)
                   'NIL)
               'NIL)))

(DEFTHM KNOWN-PACKAGE-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP
        (IMPLIES (KNOWN-PACKAGE-ALISTP X)
                 (IF (TRUE-LIST-LISTP X)
                     (ALISTP X)
                     'NIL)))

(DEFUN TIMER-ALISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (IF (CONSP (CAR X))
                   (IF (SYMBOLP (CAR (CAR X)))
                       (RATIONAL-LISTP (CDR (CAR X)))
                       'NIL)
                   'NIL)
               (TIMER-ALISTP (CDR X))
               'NIL)))

(DEFTHM TIMER-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-SYMBOL-ALISTP
        (IMPLIES (TIMER-ALISTP X)
                 (IF (TRUE-LIST-LISTP X)
                     (SYMBOL-ALISTP X)
                     'NIL)))

(DEFUN TYPED-IO-LISTP (L TYP)
       (IF (ATOM L)
           (EQUAL L 'NIL)
           (IF (IF (EQL TYP ':CHARACTER)
                   (CHARACTERP (CAR L))
                   (IF (EQL TYP ':BYTE)
                       (IF (INTEGERP (CAR L))
                           (IF (NOT (< (CAR L) '0))
                               (< (CAR L) '256)
                               'NIL)
                           'NIL)
                       (IF (EQL TYP ':OBJECT) 'T 'NIL)))
               (TYPED-IO-LISTP (CDR L) TYP)
               'NIL)))

(DEFTHM TYPED-IO-LISTP-FORWARD-TO-TRUE-LISTP
        (IMPLIES (TYPED-IO-LISTP X TYP)
                 (TRUE-LISTP X)))

(DEFUN
 OPEN-CHANNEL1 (L)
 (IF
  (TRUE-LISTP L)
  (IF
   (CONSP L)
   ((LAMBDA (HEADER L)
            (IF (TRUE-LISTP HEADER)
                (IF (EQUAL (LENGTH HEADER) '4)
                    (IF (EQ (CAR HEADER) ':HEADER)
                        (IF (MEMBER-EQ (CAR (CDR HEADER))
                                       '(:CHARACTER :BYTE :OBJECT))
                            (IF (STRINGP (CAR (CDR (CDR HEADER))))
                                (IF (INTEGERP (CAR (CDR (CDR (CDR HEADER)))))
                                    (TYPED-IO-LISTP (CDR L)
                                                    (CAR (CDR HEADER)))
                                    'NIL)
                                'NIL)
                            'NIL)
                        'NIL)
                    'NIL)
                'NIL))
    (CAR L)
    L)
   'NIL)
  'NIL))

(DEFTHM OPEN-CHANNEL1-FORWARD-TO-TRUE-LISTP-AND-CONSP
        (IMPLIES (OPEN-CHANNEL1 X)
                 (IF (TRUE-LISTP X) (CONSP X) 'NIL)))

(DEFUN OPEN-CHANNEL-LISTP (L)
       (IF (ENDP L)
           'T
           (IF (OPEN-CHANNEL1 (CDR (CAR L)))
               (OPEN-CHANNEL-LISTP (CDR L))
               'NIL)))

(DEFUN OPEN-CHANNELS-P (X)
       (IF (ORDERED-SYMBOL-ALISTP X)
           (OPEN-CHANNEL-LISTP X)
           'NIL))

(DEFTHM OPEN-CHANNELS-P-FORWARD
        (IMPLIES (OPEN-CHANNELS-P X)
                 (IF (ORDERED-SYMBOL-ALISTP X)
                     (TRUE-LIST-LISTP X)
                     'NIL)))

(DEFUN FILE-CLOCK-P (X) (NATP X))

(DEFTHM FILE-CLOCK-P-FORWARD-TO-INTEGERP
        (IMPLIES (FILE-CLOCK-P X) (NATP X)))

(DEFUN
 READABLE-FILE (X)
 (IF
    (TRUE-LISTP X)
    (IF (CONSP X)
        ((LAMBDA (KEY X)
                 (IF (TRUE-LISTP KEY)
                     (IF (EQUAL (LENGTH KEY) '3)
                         (IF (STRINGP (CAR KEY))
                             (IF (MEMBER (CAR (CDR KEY))
                                         '(:CHARACTER :BYTE :OBJECT))
                                 (IF (INTEGERP (CAR (CDR (CDR KEY))))
                                     (TYPED-IO-LISTP (CDR X) (CAR (CDR KEY)))
                                     'NIL)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL))
         (CAR X)
         X)
        'NIL)
    'NIL))

(DEFTHM READABLE-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP
        (IMPLIES (READABLE-FILE X)
                 (IF (TRUE-LISTP X) (CONSP X) 'NIL)))

(DEFUN READABLE-FILES-LISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (READABLE-FILE (CAR X))
               (READABLE-FILES-LISTP (CDR X))
               'NIL)))

(DEFTHM READABLE-FILES-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP
        (IMPLIES (READABLE-FILES-LISTP X)
                 (IF (TRUE-LIST-LISTP X)
                     (ALISTP X)
                     'NIL)))

(DEFUN READABLE-FILES-P (X) (READABLE-FILES-LISTP X))

(DEFTHM READABLE-FILES-P-FORWARD-TO-READABLE-FILES-LISTP
        (IMPLIES (READABLE-FILES-P X)
                 (READABLE-FILES-LISTP X)))

(DEFUN
 WRITTEN-FILE (X)
 (IF
  (TRUE-LISTP X)
  (IF
    (CONSP X)
    ((LAMBDA (KEY X)
             (IF (TRUE-LISTP KEY)
                 (IF (EQUAL (LENGTH KEY) '4)
                     (IF (STRINGP (CAR KEY))
                         (IF (INTEGERP (CAR (CDR (CDR KEY))))
                             (IF (INTEGERP (CAR (CDR (CDR (CDR KEY)))))
                                 (IF (MEMBER (CAR (CDR KEY))
                                             '(:CHARACTER :BYTE :OBJECT))
                                     (TYPED-IO-LISTP (CDR X) (CAR (CDR KEY)))
                                     'NIL)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 'NIL))
     (CAR X)
     X)
    'NIL)
  'NIL))

(DEFTHM WRITTEN-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP
        (IMPLIES (WRITTEN-FILE X)
                 (IF (TRUE-LISTP X) (CONSP X) 'NIL)))

(DEFUN WRITTEN-FILE-LISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (WRITTEN-FILE (CAR X))
               (WRITTEN-FILE-LISTP (CDR X))
               'NIL)))

(DEFTHM WRITTEN-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP
        (IMPLIES (WRITTEN-FILE-LISTP X)
                 (IF (TRUE-LIST-LISTP X)
                     (ALISTP X)
                     'NIL)))

(DEFUN WRITTEN-FILES-P (X) (WRITTEN-FILE-LISTP X))

(DEFTHM WRITTEN-FILES-P-FORWARD-TO-WRITTEN-FILE-LISTP
        (IMPLIES (WRITTEN-FILES-P X)
                 (WRITTEN-FILE-LISTP X)))

(DEFUN READ-FILE-LISTP1 (X)
       (IF (TRUE-LISTP X)
           (IF (EQUAL (LENGTH X) '4)
               (IF (STRINGP (CAR X))
                   (IF (MEMBER (CAR (CDR X))
                               '(:CHARACTER :BYTE :OBJECT))
                       (IF (INTEGERP (CAR (CDR (CDR X))))
                           (INTEGERP (CAR (CDR (CDR (CDR X)))))
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)
           'NIL))

(DEFTHM READ-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP
        (IMPLIES (READ-FILE-LISTP1 X)
                 (IF (TRUE-LISTP X) (CONSP X) 'NIL)))

(DEFUN READ-FILE-LISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (READ-FILE-LISTP1 (CAR X))
               (READ-FILE-LISTP (CDR X))
               'NIL)))

(DEFTHM READ-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP
        (IMPLIES (READ-FILE-LISTP X)
                 (TRUE-LIST-LISTP X)))

(DEFUN READ-FILES-P (X) (READ-FILE-LISTP X))

(DEFTHM READ-FILES-P-FORWARD-TO-READ-FILE-LISTP
        (IMPLIES (READ-FILES-P X)
                 (READ-FILE-LISTP X)))

(DEFUN WRITABLE-FILE-LISTP1 (X)
       (IF (TRUE-LISTP X)
           (IF (EQUAL (LENGTH X) '3)
               (IF (STRINGP (CAR X))
                   (IF (MEMBER (CAR (CDR X))
                               '(:CHARACTER :BYTE :OBJECT))
                       (INTEGERP (CAR (CDR (CDR X))))
                       'NIL)
                   'NIL)
               'NIL)
           'NIL))

(DEFTHM WRITABLE-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP
        (IMPLIES (WRITABLE-FILE-LISTP1 X)
                 (IF (TRUE-LISTP X) (CONSP X) 'NIL)))

(DEFUN WRITABLE-FILE-LISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (WRITABLE-FILE-LISTP1 (CAR X))
               (WRITABLE-FILE-LISTP (CDR X))
               'NIL)))

(DEFTHM WRITABLE-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP
        (IMPLIES (WRITABLE-FILE-LISTP X)
                 (TRUE-LIST-LISTP X)))

(DEFUN WRITEABLE-FILES-P (X) (WRITABLE-FILE-LISTP X))

(DEFTHM WRITEABLE-FILES-P-FORWARD-TO-WRITABLE-FILE-LISTP
        (IMPLIES (WRITEABLE-FILES-P X)
                 (WRITABLE-FILE-LISTP X)))

(DEFUN
 STATE-P1 (X)
 (IF
  (TRUE-LISTP X)
  (IF
   (EQUAL (LENGTH X) '15)
   (IF
    (OPEN-CHANNELS-P (OPEN-INPUT-CHANNELS X))
    (IF
     (OPEN-CHANNELS-P (OPEN-OUTPUT-CHANNELS X))
     (IF
      (ORDERED-SYMBOL-ALISTP (GLOBAL-TABLE X))
      (IF
       (ALL-BOUNDP
          '((ABBREV-EVISC-TUPLE . :DEFAULT)
            (ACCUMULATED-TTREE)
            (ACCUMULATED-WARNINGS)
            (ACL2-RAW-MODE-P)
            (ACL2-VERSION . "ACL2 Version 3.5")
            (AXIOMSP)
            (BDDNOTES)
            (CERTIFY-BOOK-DISABLEDP)
            (CERTIFY-BOOK-INFO)
            (CHECKPOINT-FORCED-GOALS)
            (CHECKPOINT-PROCESSORS ELIMINATE-DESTRUCTORS-CLAUSE
                                   FERTILIZE-CLAUSE GENERALIZE-CLAUSE
                                   ELIMINATE-IRRELEVANCE-CLAUSE
                                   PUSH-CLAUSE :INDUCT)
            (CHECKPOINT-SUMMARY-LIMIT NIL . 3)
            (CONNECTED-BOOK-DIRECTORY)
            (CURRENT-ACL2-WORLD)
            (CURRENT-PACKAGE . "ACL2")
            (DEBUGGER-ENABLE)
            (DEFAXIOMS-OKP-CERT . T)
            (DISTRIBUTED-BOOKS-DIR)
            (DMRP)
            (EVISC-HITP-WITHOUT-IPRINT)
            (EVISCERATE-HIDE-TERMS)
            (FMT-HARD-RIGHT-MARGIN . 77)
            (FMT-SOFT-RIGHT-MARGIN . 65)
            (GAG-MODE)
            (GAG-STATE)
            (GAG-STATE-SAVED)
            (GLOBAL-ENABLED-STRUCTURE)
            (GSTACKP)
            (GUARD-CHECKING-ON . T)
            (HONS-ENABLED)
            (HONS-READ-P . T)
            (IN-LOCAL-FLG)
            (IN-PROVE-FLG)
            (IN-VERIFY-FLG)
            (INFIXP)
            (INHIBIT-OUTPUT-LST SUMMARY)
            (INHIBIT-OUTPUT-LST-STACK)
            (IPRINT-AR (:HEADER :DIMENSIONS (10001)
                                :MAXIMUM-LENGTH 40004
                                :DEFAULT NIL
                                :NAME IPRINT-AR
                                :ORDER :NONE)
                       (0 0))
            (IPRINT-HARD-BOUND . 10000)
            (IPRINT-SOFT-BOUND . 1000)
            (KEEP-TMP-FILES)
            (LAST-MAKE-EVENT-EXPANSION)
            (LD-LEVEL . 0)
            (LD-REDEFINITION-ACTION)
            (LD-SKIP-PROOFSP)
            (LOGIC-FNS-WITH-RAW-CODE MOD-EXPT HEADER SEARCH-FN STATE-P1
                                     AREF2 AREF1 MFC-ANCESTORS FGETPROP
                                     GETENV$ WORMHOLE1 ASET2 SGETPROP SETENV$
                                     GETPROPS COMPRESS1 TIME-LIMIT4-REACHED-P
                                     FMT-TO-COMMENT-WINDOW
                                     LEN MFC-CLAUSE CPU-CORE-COUNT
                                     NONNEGATIVE-INTEGER-QUOTIENT
                                     CHECK-PRINT-BASE RETRACT-WORLD
                                     ASET1 ARRAY1P BOOLE$ ARRAY2P STRIP-CDRS
                                     COMPRESS2 STRIP-CARS WORLDP WORMHOLE-P
                                     MFC-TYPE-ALIST MAY-NEED-SLASHES-FN
                                     FMT-TO-COMMENT-WINDOW!
                                     HAS-PROPSP HARD-ERROR
                                     ABORT! MFC-RDEPTH FLUSH-COMPRESS
                                     ALPHORDER EXTEND-WORLD USER-STOBJ-ALIST
                                     READ-ACL2-ORACLE UPDATE-USER-STOBJ-ALIST
                                     DECREMENT-BIG-CLOCK
                                     PUT-GLOBAL CLOSE-INPUT-CHANNEL
                                     MAKUNBOUND-GLOBAL OPEN-INPUT-CHANNEL-P1
                                     BOUNDP-GLOBAL1 GLOBAL-TABLE-CARS1
                                     EXTEND-T-STACK LIST-ALL-PACKAGE-NAMES
                                     CLOSE-OUTPUT-CHANNEL WRITE-BYTE$
                                     SHRINK-T-STACK ASET-32-BIT-INTEGER-STACK
                                     GET-GLOBAL 32-BIT-INTEGER-STACK-LENGTH1
                                     EXTEND-32-BIT-INTEGER-STACK ASET-T-STACK
                                     WITH-PROVER-TIME-LIMIT AREF-T-STACK
                                     READ-CHAR$ AREF-32-BIT-INTEGER-STACK
                                     OPEN-OUTPUT-CHANNEL-P1
                                     READ-OBJECT BIG-CLOCK-NEGATIVE-P
                                     PEEK-CHAR$ SHRINK-32-BIT-INTEGER-STACK
                                     READ-RUN-TIME READ-BYTE$ EC-CALL
                                     PROG2$ READ-IDATE TIME$ PRINT-OBJECT$
                                     T-STACK-LENGTH1 MUST-BE-EQUAL ZPF
                                     IDENTITY ENDP NTHCDR LAST REVAPPEND NULL
                                     BUTLAST STRING MEMBER NOT MOD PLUSP ATOM
                                     LISTP ZP FLOOR CEILING TRUNCATE ROUND
                                     REM REMOVE REMOVE-DUPLICATES LOGBITP
                                     ASH LOGCOUNT SIGNUM INTEGER-LENGTH
                                     EXPT SUBSETP SUBSTITUTE ZEROP
                                     MINUSP ODDP EVENP = /= MAX MIN CONJUGATE
                                     LOGANDC1 LOGANDC2 LOGNAND LOGNOR LOGNOT
                                     LOGORC1 LOGORC2 LOGTEST POSITION ABS
                                     STRING-EQUAL STRING< STRING> STRING<=
                                     STRING>= STRING-UPCASE STRING-DOWNCASE
                                     KEYWORDP EQ EQL CHAR SUBST SUBLIS
                                     ACONS ASSOC RASSOC NTH SUBSEQ LENGTH
                                     REVERSE ZIP STANDARD-CHAR-P ALPHA-CHAR-P
                                     UPPER-CASE-P LOWER-CASE-P CHAR< CHAR>
                                     CHAR<= CHAR>= CHAR-EQUAL CHAR-UPCASE
                                     CHAR-DOWNCASE HONS-READ-OBJECT
                                     AND-LIST OR-LIST RANDOM$)
            (MACROS-WITH-RAW-CODE MBE
                                  THEORY-INVARIANT SET-LET*-ABSTRACTIONP
                                  DEFAXIOM SET-BOGUS-MUTUAL-RECURSION-OK
                                  SET-RULER-EXTENDERS
                                  DELETE-INCLUDE-BOOK-DIR CERTIFY-BOOK
                                  PROGN! F-PUT-GLOBAL PUSH-UNTOUCHABLE
                                  SET-BACKCHAIN-LIMIT SET-DEFAULT-HINTS!
                                  DEFTHEORY PSTK VERIFY-GUARDS
                                  DEFCHOOSE SET-DEFAULT-BACKCHAIN-LIMIT
                                  SET-STATE-OK SET-IGNORE-OK
                                  SET-NON-LINEARP WITH-OUTPUT
                                  SET-COMPILE-FNS ADD-INCLUDE-BOOK-DIR
                                  CLEAR-PSTK ADD-CUSTOM-KEYWORD-HINT
                                  INITIAL-GSTACK ASSIGN-WORMHOLE-OUTPUT
                                  ACL2-UNWIND-PROTECT
                                  SET-WELL-FOUNDED-RELATION
                                  CATCH-TIME-LIMIT4 DEFUNS
                                  ADD-DEFAULT-HINTS! LOCAL ENCAPSULATE
                                  REMOVE-DEFAULT-HINTS! INCLUDE-BOOK
                                  PPROGN SET-ENFORCE-REDUNDANCY
                                  SET-IGNORE-DOC-STRING-ERROR LOGIC
                                  ER DEFLABEL MV-LET PROGRAM VALUE-TRIPLE
                                  SET-BODY COMP SET-BOGUS-DEFUN-HINTS-OK
                                  DMR-STOP DEFPKG SET-MEASURE-FUNCTION
                                  SET-INHIBIT-WARNINGS DEFTHM MV
                                  F-BIG-CLOCK-NEGATIVE-P RESET-PREHISTORY
                                  MUTUAL-RECURSION SET-REWRITE-STACK-LIMIT
                                  ADD-MATCH-FREE-OVERRIDE
                                  SET-INHIBIT-OUTPUT-LST
                                  SET-MATCH-FREE-DEFAULT
                                  THE-MV TABLE IN-ARITHMETIC-THEORY
                                  SET-CASE-SPLIT-LIMITATIONS
                                  SET-IRRELEVANT-FORMALS-OK
                                  REMOVE-UNTOUCHABLE
                                  IN-THEORY WITH-OUTPUT-FORCED
                                  DMR-START REWRITE-ENTRY
                                  SKIP-PROOFS F-BOUNDP-GLOBAL
                                  MAKE-EVENT SET-VERIFY-GUARDS-EAGERNESS
                                  WORMHOLE VERIFY-TERMINATION-BOOT-STRAP
                                  START-PROOF-TREE F-DECREMENT-BIG-CLOCK
                                  DEFSTOBJ DEFUND DEFTTAG
                                  DEFDOC PUSH-GFRAME DEFTHMD F-GET-GLOBAL
                                  SET-NU-REWRITER-MODE CAAR CADR
                                  CDAR CDDR CAAAR CAADR CADAR CADDR CDAAR
                                  CDADR CDDAR CDDDR CAAAAR CAAADR CAADAR
                                  CAADDR CADAAR CADADR CADDAR CADDDR
                                  CDAAAR CDAADR CDADAR CDADDR CDDAAR
                                  CDDADR CDDDAR CDDDDR REST MAKE-LIST LIST
                                  OR AND * LOGIOR LOGXOR LOGAND SEARCH
                                  LOGEQV CONCATENATE LET* DEFUN THE > <=
                                  >= + - / 1+ 1- PROGN DEFMACRO COND CASE
                                  LIST* APPEND DEFCONST IN-PACKAGE INTERN
                                  FIRST SECOND THIRD FOURTH FIFTH SIXTH
                                  SEVENTH EIGHTH NINTH TENTH DIGIT-CHAR-P
                                  UNMEMOIZE HONS-LET MEMOIZE-LET MEMOIZE
                                  DEFUNS-STD DEFTHM-STD DEFUN-STD POR
                                  PAND PLET PARGS TRACE! WITH-LIVE-STATE
                                  WITH-OUTPUT-OBJECT-CHANNEL-SHARING)
            (MAIN-TIMER . 0)
            (MAKE-EVENT-DEBUG)
            (MAKE-EVENT-DEBUG-DEPTH . 0)
            (MATCH-FREE-ERROR)
            (MORE-DOC-MAX-LINES . 45)
            (MORE-DOC-MIN-LINES . 35)
            (MORE-DOC-STATE)
            (MSWINDOWS-DRIVE)
            (PACKAGES-CREATED-BY-DEFPKG)
            (PARALLEL-EVALUATION-ENABLED)
            (PC-OUTPUT)
            (PPR-FLAT-RIGHT-MARGIN . 40)
            (PRINT-BASE . 10)
            (PRINT-CASE . :UPCASE)
            (PRINT-CIRCLE)
            (PRINT-CLAUSE-IDS)
            (PRINT-DOC-START-COLUMN . 15)
            (PRINT-ESCAPE . T)
            (PRINT-LENGTH)
            (PRINT-LEVEL)
            (PRINT-LINES)
            (PRINT-PRETTY)
            (PRINT-RADIX)
            (PRINT-READABLY)
            (PRINT-RIGHT-MARGIN)
            (PROGRAM-FNS-WITH-RAW-CODE
                 RELIEVE-HYP-SYNP
                 APPLY-ABBREVS-TO-LAMBDA-STACK1
                 GOOD-BYE-FN NTH-UPDATE-REWRITER
                 EV-W-LST SIMPLIFY-CLAUSE1
                 EV-REC-ACL2-UNWIND-PROTECT
                 ALLOCATE-FIXNUM-RANGE TRACE$-FN-GENERAL
                 EV-FNCALL! OPEN-TRACE-FILE-FN
                 SET-TRACE-EVISC-TUPLE EV-FNCALL-W
                 EV-REC SETUP-SIMPLIFY-CLAUSE-POT-LST1
                 SAVE-EXEC CW-GSTACK-FN
                 RECOMPRESS-GLOBAL-ENABLED-STRUCTURE EV-W
                 VERBOSE-PSTACK USER-STOBJ-ALIST-SAFE
                 COMP-FN FMT-PPR GET-MEMO
                 ACL2-RAW-EVAL PSTACK-FN DMR-START-FN
                 MEMO-EXIT MEMO-KEY1 SYS-CALL-STATUS
                 EV-FNCALL-META SET-DEBUGGER-ENABLE-FN
                 LD-LOOP PRINT-SUMMARY
                 EV EV-LST ALLEGRO-ALLOCATE-SLOWLY-FN
                 CERTIFY-BOOK-FN
                 TRANSLATE11-FLET-ALIST1 INCLUDE-BOOK-FN
                 FMT1 FLSZ SET-W PROVE-LOOP CHK-VIRGIN
                 W-OF-ANY-STATE PRINT-NEWLINE-FOR-TIME$
                 LAMBDA-ABSTRACT LD-FN-BODY UNTRANSLATE
                 LONGEST-COMMON-TAIL-LENGTH-REC
                 COMPILE-FUNCTION UNTRANSLATE-LST EV-SYNP
                 ADD-POLYS DMR-STOP-FN LD-PRINT-RESULTS
                 APPLY-ABBREVS-TO-LAMBDA-STACK
                 BREAK$ FLPR CLOSE-TRACE-FILE-FN
                 EV-FNCALL-REC SYS-CALL EV-FNCALL LD-FN0
                 LD-FN WRITE-EXPANSION-FILE LATCH-STOBJS1
                 CHK-PACKAGE-REINCARNATION-IMPORT-RESTRICTIONS
                 UNTRACE$-FN1 BDD-TOP
                 GC$-FN DEFSTOBJ-FIELD-FNS-RAW-DEFS
                 EXPANSION-ALIST-PKG-NAMES
                 TIMES-MOD-M31 PRINT-CALL-HISTORY
                 IPRINT-AR-AREF1 PROVE MAKE-EVENT-FN)
            (PROMPT-FUNCTION . DEFAULT-PRINT-PROMPT)
            (PROMPT-MEMO)
            (PROOF-TREE)
            (PROOF-TREE-BUFFER-WIDTH . 65)
            (PROOF-TREE-CTX)
            (PROOF-TREE-INDENT . "|  ")
            (PROOF-TREE-START-PRINTED)
            (PROOFS-CO .
                       ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (RAW-ARITY-ALIST)
            (RAW-PROOF-FORMAT)
            (REDO-FLAT-FAIL)
            (REDO-FLAT-SUCC)
            (REDUNDANT-WITH-RAW-CODE-OKP)
            (SAFE-MODE)
            (SAVED-OUTPUT-P)
            (SAVED-OUTPUT-REVERSED)
            (SAVED-OUTPUT-TOKEN-LST)
            (SHOW-CUSTOM-KEYWORD-HINT-EXPANSION)
            (SKIP-NOTIFY-ON-DEFTTAG)
            (SKIP-PROOFS-BY-SYSTEM)
            (SKIP-PROOFS-OKP-CERT . T)
            (SLOW-ARRAY-ACTION . :BREAK)
            (STANDARD-CO .
                         ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (STANDARD-OI .
                         ACL2-OUTPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
            (SUPPRESS-COMPILE)
            (TAINTED-OKP)
            (TEMP-TOUCHABLE-FNS)
            (TEMP-TOUCHABLE-VARS)
            (TERM-EVISC-TUPLE . :DEFAULT)
            (TIMER-ALIST)
            (TMP-DIR)
            (TRACE-CO .
                      ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (TRACE-LEVEL . 0)
            (TRACE-SPECS)
            (TRANSLATE-ERROR-DEPTH . -1)
            (TRIPLE-PRINT-PREFIX . " ")
            (TTAGS-ALLOWED . :ALL)
            (UNDONE-WORLDS-KILL-RING NIL NIL NIL)
            (USER-HOME-DIR)
            (WINDOW-INTERFACE-POSTLUDE
                 .
                 "#>\\>#<\\<e(acl2-window-postlude ?~sw ~xt ~xp)#>\\>")
            (WINDOW-INTERFACE-PRELUDE
                 .
                 "~%#<\\<e(acl2-window-prelude ?~sw ~xc)#>\\>#<\\<~sw")
            (WINDOW-INTERFACEP)
            (WORMHOLE-NAME)
            (WORMHOLE-OUTPUT)
            (WRITES-OKP . T))
          (GLOBAL-TABLE X))
       (IF
        (WORLDP (CDR (ASSOC 'CURRENT-ACL2-WORLD
                            (GLOBAL-TABLE X))))
        (IF
         (SYMBOL-ALISTP (FGETPROP 'ACL2-DEFAULTS-TABLE
                                  'TABLE-ALIST
                                  'NIL
                                  (CDR (ASSOC 'CURRENT-ACL2-WORLD
                                              (GLOBAL-TABLE X)))))
         (IF
          (TIMER-ALISTP (CDR (ASSOC 'TIMER-ALIST (GLOBAL-TABLE X))))
          (IF
           (KNOWN-PACKAGE-ALISTP (FGETPROP 'KNOWN-PACKAGE-ALIST
                                           'GLOBAL-VALUE
                                           'NIL
                                           (CDR (ASSOC 'CURRENT-ACL2-WORLD
                                                       (GLOBAL-TABLE X)))))
           (IF
            (TRUE-LISTP (T-STACK X))
            (IF
             (32-BIT-INTEGER-LISTP (32-BIT-INTEGER-STACK X))
             (IF
              (INTEGERP (BIG-CLOCK-ENTRY X))
              (IF
               (INTEGER-LISTP (IDATES X))
               (IF
                (TRUE-LISTP (ACL2-ORACLE X))
                (IF
                 (FILE-CLOCK-P (FILE-CLOCK X))
                 (IF
                  (READABLE-FILES-P (READABLE-FILES X))
                  (IF
                   (WRITTEN-FILES-P (WRITTEN-FILES X))
                   (IF
                     (READ-FILES-P (READ-FILES X))
                     (IF (WRITEABLE-FILES-P (WRITEABLE-FILES X))
                         (IF (TRUE-LIST-LISTP (LIST-ALL-PACKAGE-NAMES-LST X))
                             (SYMBOL-ALISTP (USER-STOBJ-ALIST1 X))
                             'NIL)
                         'NIL)
                     'NIL)
                   'NIL)
                  'NIL)
                 'NIL)
                'NIL)
               'NIL)
              'NIL)
             'NIL)
            'NIL)
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

(DEFTHM
 STATE-P1-FORWARD
 (IMPLIES
  (STATE-P1 X)
  (IF
   (TRUE-LISTP X)
   (IF
    (EQUAL (LENGTH X) '15)
    (IF
     (OPEN-CHANNELS-P (NTH '0 X))
     (IF
      (OPEN-CHANNELS-P (NTH '1 X))
      (IF
       (ORDERED-SYMBOL-ALISTP (NTH '2 X))
       (IF
        (ALL-BOUNDP
          '((ABBREV-EVISC-TUPLE . :DEFAULT)
            (ACCUMULATED-TTREE)
            (ACCUMULATED-WARNINGS)
            (ACL2-RAW-MODE-P)
            (ACL2-VERSION . "ACL2 Version 3.5")
            (AXIOMSP)
            (BDDNOTES)
            (CERTIFY-BOOK-DISABLEDP)
            (CERTIFY-BOOK-INFO)
            (CHECKPOINT-FORCED-GOALS)
            (CHECKPOINT-PROCESSORS ELIMINATE-DESTRUCTORS-CLAUSE
                                   FERTILIZE-CLAUSE GENERALIZE-CLAUSE
                                   ELIMINATE-IRRELEVANCE-CLAUSE
                                   PUSH-CLAUSE :INDUCT)
            (CHECKPOINT-SUMMARY-LIMIT NIL . 3)
            (CONNECTED-BOOK-DIRECTORY)
            (CURRENT-ACL2-WORLD)
            (CURRENT-PACKAGE . "ACL2")
            (DEBUGGER-ENABLE)
            (DEFAXIOMS-OKP-CERT . T)
            (DISTRIBUTED-BOOKS-DIR)
            (DMRP)
            (EVISC-HITP-WITHOUT-IPRINT)
            (EVISCERATE-HIDE-TERMS)
            (FMT-HARD-RIGHT-MARGIN . 77)
            (FMT-SOFT-RIGHT-MARGIN . 65)
            (GAG-MODE)
            (GAG-STATE)
            (GAG-STATE-SAVED)
            (GLOBAL-ENABLED-STRUCTURE)
            (GSTACKP)
            (GUARD-CHECKING-ON . T)
            (HONS-ENABLED)
            (HONS-READ-P . T)
            (IN-LOCAL-FLG)
            (IN-PROVE-FLG)
            (IN-VERIFY-FLG)
            (INFIXP)
            (INHIBIT-OUTPUT-LST SUMMARY)
            (INHIBIT-OUTPUT-LST-STACK)
            (IPRINT-AR (:HEADER :DIMENSIONS (10001)
                                :MAXIMUM-LENGTH 40004
                                :DEFAULT NIL
                                :NAME IPRINT-AR
                                :ORDER :NONE)
                       (0 0))
            (IPRINT-HARD-BOUND . 10000)
            (IPRINT-SOFT-BOUND . 1000)
            (KEEP-TMP-FILES)
            (LAST-MAKE-EVENT-EXPANSION)
            (LD-LEVEL . 0)
            (LD-REDEFINITION-ACTION)
            (LD-SKIP-PROOFSP)
            (LOGIC-FNS-WITH-RAW-CODE MOD-EXPT HEADER SEARCH-FN STATE-P1
                                     AREF2 AREF1 MFC-ANCESTORS FGETPROP
                                     GETENV$ WORMHOLE1 ASET2 SGETPROP SETENV$
                                     GETPROPS COMPRESS1 TIME-LIMIT4-REACHED-P
                                     FMT-TO-COMMENT-WINDOW
                                     LEN MFC-CLAUSE CPU-CORE-COUNT
                                     NONNEGATIVE-INTEGER-QUOTIENT
                                     CHECK-PRINT-BASE RETRACT-WORLD
                                     ASET1 ARRAY1P BOOLE$ ARRAY2P STRIP-CDRS
                                     COMPRESS2 STRIP-CARS WORLDP WORMHOLE-P
                                     MFC-TYPE-ALIST MAY-NEED-SLASHES-FN
                                     FMT-TO-COMMENT-WINDOW!
                                     HAS-PROPSP HARD-ERROR
                                     ABORT! MFC-RDEPTH FLUSH-COMPRESS
                                     ALPHORDER EXTEND-WORLD USER-STOBJ-ALIST
                                     READ-ACL2-ORACLE UPDATE-USER-STOBJ-ALIST
                                     DECREMENT-BIG-CLOCK
                                     PUT-GLOBAL CLOSE-INPUT-CHANNEL
                                     MAKUNBOUND-GLOBAL OPEN-INPUT-CHANNEL-P1
                                     BOUNDP-GLOBAL1 GLOBAL-TABLE-CARS1
                                     EXTEND-T-STACK LIST-ALL-PACKAGE-NAMES
                                     CLOSE-OUTPUT-CHANNEL WRITE-BYTE$
                                     SHRINK-T-STACK ASET-32-BIT-INTEGER-STACK
                                     GET-GLOBAL 32-BIT-INTEGER-STACK-LENGTH1
                                     EXTEND-32-BIT-INTEGER-STACK ASET-T-STACK
                                     WITH-PROVER-TIME-LIMIT AREF-T-STACK
                                     READ-CHAR$ AREF-32-BIT-INTEGER-STACK
                                     OPEN-OUTPUT-CHANNEL-P1
                                     READ-OBJECT BIG-CLOCK-NEGATIVE-P
                                     PEEK-CHAR$ SHRINK-32-BIT-INTEGER-STACK
                                     READ-RUN-TIME READ-BYTE$ EC-CALL
                                     PROG2$ READ-IDATE TIME$ PRINT-OBJECT$
                                     T-STACK-LENGTH1 MUST-BE-EQUAL ZPF
                                     IDENTITY ENDP NTHCDR LAST REVAPPEND NULL
                                     BUTLAST STRING MEMBER NOT MOD PLUSP ATOM
                                     LISTP ZP FLOOR CEILING TRUNCATE ROUND
                                     REM REMOVE REMOVE-DUPLICATES LOGBITP
                                     ASH LOGCOUNT SIGNUM INTEGER-LENGTH
                                     EXPT SUBSETP SUBSTITUTE ZEROP
                                     MINUSP ODDP EVENP = /= MAX MIN CONJUGATE
                                     LOGANDC1 LOGANDC2 LOGNAND LOGNOR LOGNOT
                                     LOGORC1 LOGORC2 LOGTEST POSITION ABS
                                     STRING-EQUAL STRING< STRING> STRING<=
                                     STRING>= STRING-UPCASE STRING-DOWNCASE
                                     KEYWORDP EQ EQL CHAR SUBST SUBLIS
                                     ACONS ASSOC RASSOC NTH SUBSEQ LENGTH
                                     REVERSE ZIP STANDARD-CHAR-P ALPHA-CHAR-P
                                     UPPER-CASE-P LOWER-CASE-P CHAR< CHAR>
                                     CHAR<= CHAR>= CHAR-EQUAL CHAR-UPCASE
                                     CHAR-DOWNCASE HONS-READ-OBJECT
                                     AND-LIST OR-LIST RANDOM$)
            (MACROS-WITH-RAW-CODE MBE
                                  THEORY-INVARIANT SET-LET*-ABSTRACTIONP
                                  DEFAXIOM SET-BOGUS-MUTUAL-RECURSION-OK
                                  SET-RULER-EXTENDERS
                                  DELETE-INCLUDE-BOOK-DIR CERTIFY-BOOK
                                  PROGN! F-PUT-GLOBAL PUSH-UNTOUCHABLE
                                  SET-BACKCHAIN-LIMIT SET-DEFAULT-HINTS!
                                  DEFTHEORY PSTK VERIFY-GUARDS
                                  DEFCHOOSE SET-DEFAULT-BACKCHAIN-LIMIT
                                  SET-STATE-OK SET-IGNORE-OK
                                  SET-NON-LINEARP WITH-OUTPUT
                                  SET-COMPILE-FNS ADD-INCLUDE-BOOK-DIR
                                  CLEAR-PSTK ADD-CUSTOM-KEYWORD-HINT
                                  INITIAL-GSTACK ASSIGN-WORMHOLE-OUTPUT
                                  ACL2-UNWIND-PROTECT
                                  SET-WELL-FOUNDED-RELATION
                                  CATCH-TIME-LIMIT4 DEFUNS
                                  ADD-DEFAULT-HINTS! LOCAL ENCAPSULATE
                                  REMOVE-DEFAULT-HINTS! INCLUDE-BOOK
                                  PPROGN SET-ENFORCE-REDUNDANCY
                                  SET-IGNORE-DOC-STRING-ERROR LOGIC
                                  ER DEFLABEL MV-LET PROGRAM VALUE-TRIPLE
                                  SET-BODY COMP SET-BOGUS-DEFUN-HINTS-OK
                                  DMR-STOP DEFPKG SET-MEASURE-FUNCTION
                                  SET-INHIBIT-WARNINGS DEFTHM MV
                                  F-BIG-CLOCK-NEGATIVE-P RESET-PREHISTORY
                                  MUTUAL-RECURSION SET-REWRITE-STACK-LIMIT
                                  ADD-MATCH-FREE-OVERRIDE
                                  SET-INHIBIT-OUTPUT-LST
                                  SET-MATCH-FREE-DEFAULT
                                  THE-MV TABLE IN-ARITHMETIC-THEORY
                                  SET-CASE-SPLIT-LIMITATIONS
                                  SET-IRRELEVANT-FORMALS-OK
                                  REMOVE-UNTOUCHABLE
                                  IN-THEORY WITH-OUTPUT-FORCED
                                  DMR-START REWRITE-ENTRY
                                  SKIP-PROOFS F-BOUNDP-GLOBAL
                                  MAKE-EVENT SET-VERIFY-GUARDS-EAGERNESS
                                  WORMHOLE VERIFY-TERMINATION-BOOT-STRAP
                                  START-PROOF-TREE F-DECREMENT-BIG-CLOCK
                                  DEFSTOBJ DEFUND DEFTTAG
                                  DEFDOC PUSH-GFRAME DEFTHMD F-GET-GLOBAL
                                  SET-NU-REWRITER-MODE CAAR CADR
                                  CDAR CDDR CAAAR CAADR CADAR CADDR CDAAR
                                  CDADR CDDAR CDDDR CAAAAR CAAADR CAADAR
                                  CAADDR CADAAR CADADR CADDAR CADDDR
                                  CDAAAR CDAADR CDADAR CDADDR CDDAAR
                                  CDDADR CDDDAR CDDDDR REST MAKE-LIST LIST
                                  OR AND * LOGIOR LOGXOR LOGAND SEARCH
                                  LOGEQV CONCATENATE LET* DEFUN THE > <=
                                  >= + - / 1+ 1- PROGN DEFMACRO COND CASE
                                  LIST* APPEND DEFCONST IN-PACKAGE INTERN
                                  FIRST SECOND THIRD FOURTH FIFTH SIXTH
                                  SEVENTH EIGHTH NINTH TENTH DIGIT-CHAR-P
                                  UNMEMOIZE HONS-LET MEMOIZE-LET MEMOIZE
                                  DEFUNS-STD DEFTHM-STD DEFUN-STD POR
                                  PAND PLET PARGS TRACE! WITH-LIVE-STATE
                                  WITH-OUTPUT-OBJECT-CHANNEL-SHARING)
            (MAIN-TIMER . 0)
            (MAKE-EVENT-DEBUG)
            (MAKE-EVENT-DEBUG-DEPTH . 0)
            (MATCH-FREE-ERROR)
            (MORE-DOC-MAX-LINES . 45)
            (MORE-DOC-MIN-LINES . 35)
            (MORE-DOC-STATE)
            (MSWINDOWS-DRIVE)
            (PACKAGES-CREATED-BY-DEFPKG)
            (PARALLEL-EVALUATION-ENABLED)
            (PC-OUTPUT)
            (PPR-FLAT-RIGHT-MARGIN . 40)
            (PRINT-BASE . 10)
            (PRINT-CASE . :UPCASE)
            (PRINT-CIRCLE)
            (PRINT-CLAUSE-IDS)
            (PRINT-DOC-START-COLUMN . 15)
            (PRINT-ESCAPE . T)
            (PRINT-LENGTH)
            (PRINT-LEVEL)
            (PRINT-LINES)
            (PRINT-PRETTY)
            (PRINT-RADIX)
            (PRINT-READABLY)
            (PRINT-RIGHT-MARGIN)
            (PROGRAM-FNS-WITH-RAW-CODE
                 RELIEVE-HYP-SYNP
                 APPLY-ABBREVS-TO-LAMBDA-STACK1
                 GOOD-BYE-FN NTH-UPDATE-REWRITER
                 EV-W-LST SIMPLIFY-CLAUSE1
                 EV-REC-ACL2-UNWIND-PROTECT
                 ALLOCATE-FIXNUM-RANGE TRACE$-FN-GENERAL
                 EV-FNCALL! OPEN-TRACE-FILE-FN
                 SET-TRACE-EVISC-TUPLE EV-FNCALL-W
                 EV-REC SETUP-SIMPLIFY-CLAUSE-POT-LST1
                 SAVE-EXEC CW-GSTACK-FN
                 RECOMPRESS-GLOBAL-ENABLED-STRUCTURE EV-W
                 VERBOSE-PSTACK USER-STOBJ-ALIST-SAFE
                 COMP-FN FMT-PPR GET-MEMO
                 ACL2-RAW-EVAL PSTACK-FN DMR-START-FN
                 MEMO-EXIT MEMO-KEY1 SYS-CALL-STATUS
                 EV-FNCALL-META SET-DEBUGGER-ENABLE-FN
                 LD-LOOP PRINT-SUMMARY
                 EV EV-LST ALLEGRO-ALLOCATE-SLOWLY-FN
                 CERTIFY-BOOK-FN
                 TRANSLATE11-FLET-ALIST1 INCLUDE-BOOK-FN
                 FMT1 FLSZ SET-W PROVE-LOOP CHK-VIRGIN
                 W-OF-ANY-STATE PRINT-NEWLINE-FOR-TIME$
                 LAMBDA-ABSTRACT LD-FN-BODY UNTRANSLATE
                 LONGEST-COMMON-TAIL-LENGTH-REC
                 COMPILE-FUNCTION UNTRANSLATE-LST EV-SYNP
                 ADD-POLYS DMR-STOP-FN LD-PRINT-RESULTS
                 APPLY-ABBREVS-TO-LAMBDA-STACK
                 BREAK$ FLPR CLOSE-TRACE-FILE-FN
                 EV-FNCALL-REC SYS-CALL EV-FNCALL LD-FN0
                 LD-FN WRITE-EXPANSION-FILE LATCH-STOBJS1
                 CHK-PACKAGE-REINCARNATION-IMPORT-RESTRICTIONS
                 UNTRACE$-FN1 BDD-TOP
                 GC$-FN DEFSTOBJ-FIELD-FNS-RAW-DEFS
                 EXPANSION-ALIST-PKG-NAMES
                 TIMES-MOD-M31 PRINT-CALL-HISTORY
                 IPRINT-AR-AREF1 PROVE MAKE-EVENT-FN)
            (PROMPT-FUNCTION . DEFAULT-PRINT-PROMPT)
            (PROMPT-MEMO)
            (PROOF-TREE)
            (PROOF-TREE-BUFFER-WIDTH . 65)
            (PROOF-TREE-CTX)
            (PROOF-TREE-INDENT . "|  ")
            (PROOF-TREE-START-PRINTED)
            (PROOFS-CO .
                       ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (RAW-ARITY-ALIST)
            (RAW-PROOF-FORMAT)
            (REDO-FLAT-FAIL)
            (REDO-FLAT-SUCC)
            (REDUNDANT-WITH-RAW-CODE-OKP)
            (SAFE-MODE)
            (SAVED-OUTPUT-P)
            (SAVED-OUTPUT-REVERSED)
            (SAVED-OUTPUT-TOKEN-LST)
            (SHOW-CUSTOM-KEYWORD-HINT-EXPANSION)
            (SKIP-NOTIFY-ON-DEFTTAG)
            (SKIP-PROOFS-BY-SYSTEM)
            (SKIP-PROOFS-OKP-CERT . T)
            (SLOW-ARRAY-ACTION . :BREAK)
            (STANDARD-CO .
                         ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (STANDARD-OI .
                         ACL2-OUTPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
            (SUPPRESS-COMPILE)
            (TAINTED-OKP)
            (TEMP-TOUCHABLE-FNS)
            (TEMP-TOUCHABLE-VARS)
            (TERM-EVISC-TUPLE . :DEFAULT)
            (TIMER-ALIST)
            (TMP-DIR)
            (TRACE-CO .
                      ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (TRACE-LEVEL . 0)
            (TRACE-SPECS)
            (TRANSLATE-ERROR-DEPTH . -1)
            (TRIPLE-PRINT-PREFIX . " ")
            (TTAGS-ALLOWED . :ALL)
            (UNDONE-WORLDS-KILL-RING NIL NIL NIL)
            (USER-HOME-DIR)
            (WINDOW-INTERFACE-POSTLUDE
                 .
                 "#>\\>#<\\<e(acl2-window-postlude ?~sw ~xt ~xp)#>\\>")
            (WINDOW-INTERFACE-PRELUDE
                 .
                 "~%#<\\<e(acl2-window-prelude ?~sw ~xc)#>\\>#<\\<~sw")
            (WINDOW-INTERFACEP)
            (WORMHOLE-NAME)
            (WORMHOLE-OUTPUT)
            (WRITES-OKP . T))
          (NTH '2 X))
        (IF
         (WORLDP (CDR (ASSOC 'CURRENT-ACL2-WORLD (NTH '2 X))))
         (IF
          (SYMBOL-ALISTP (FGETPROP 'ACL2-DEFAULTS-TABLE
                                   'TABLE-ALIST
                                   'NIL
                                   (CDR (ASSOC 'CURRENT-ACL2-WORLD
                                               (NTH '2 X)))))
          (IF
           (TIMER-ALISTP (CDR (ASSOC 'TIMER-ALIST (NTH '2 X))))
           (IF
            (KNOWN-PACKAGE-ALISTP (FGETPROP 'KNOWN-PACKAGE-ALIST
                                            'GLOBAL-VALUE
                                            'NIL
                                            (CDR (ASSOC 'CURRENT-ACL2-WORLD
                                                        (NTH '2 X)))))
            (IF
             (TRUE-LISTP (NTH '3 X))
             (IF
              (32-BIT-INTEGER-LISTP (NTH '4 X))
              (IF
                (INTEGERP (NTH '5 X))
                (IF (INTEGER-LISTP (NTH '6 X))
                    (IF (TRUE-LISTP (NTH '7 X))
                        (IF (FILE-CLOCK-P (NTH '8 X))
                            (IF (READABLE-FILES-P (NTH '9 X))
                                (IF (WRITTEN-FILES-P (NTH '10 X))
                                    (IF (READ-FILES-P (NTH '11 X))
                                        (IF (WRITEABLE-FILES-P (NTH '12 X))
                                            (IF (TRUE-LIST-LISTP (NTH '13 X))
                                                (SYMBOL-ALISTP (NTH '14 X))
                                                'NIL)
                                            'NIL)
                                        'NIL)
                                    'NIL)
                                'NIL)
                            'NIL)
                        'NIL)
                    'NIL)
                'NIL)
              'NIL)
             'NIL)
            'NIL)
           'NIL)
          'NIL)
         'NIL)
        'NIL)
       'NIL)
      'NIL)
     'NIL)
    'NIL)
   'NIL)))

(DEFUN STATE-P (STATE-STATE) (STATE-P1 STATE-STATE))

(DEFTHM STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1
        (IMPLIES (STATE-P STATE-STATE)
                 (STATE-P1 STATE-STATE)))

(DEFUN
 BUILD-STATE1
 (OPEN-INPUT-CHANNELS OPEN-OUTPUT-CHANNELS
                      GLOBAL-TABLE T-STACK
                      32-BIT-INTEGER-STACK BIG-CLOCK IDATES
                      ACL2-ORACLE FILE-CLOCK READABLE-FILES
                      WRITTEN-FILES READ-FILES WRITEABLE-FILES
                      LIST-ALL-PACKAGE-NAMES-LST
                      USER-STOBJ-ALIST)
 ((LAMBDA
   (S)
   (IF
     (STATE-P1 S)
     S
     '(NIL NIL
           ((ABBREV-EVISC-TUPLE . :DEFAULT)
            (ACCUMULATED-TTREE)
            (ACCUMULATED-WARNINGS)
            (ACL2-RAW-MODE-P)
            (ACL2-VERSION . "ACL2 Version 3.5")
            (AXIOMSP)
            (BDDNOTES)
            (CERTIFY-BOOK-DISABLEDP)
            (CERTIFY-BOOK-INFO)
            (CHECKPOINT-FORCED-GOALS)
            (CHECKPOINT-PROCESSORS ELIMINATE-DESTRUCTORS-CLAUSE
                                   FERTILIZE-CLAUSE GENERALIZE-CLAUSE
                                   ELIMINATE-IRRELEVANCE-CLAUSE
                                   PUSH-CLAUSE :INDUCT)
            (CHECKPOINT-SUMMARY-LIMIT NIL . 3)
            (CONNECTED-BOOK-DIRECTORY)
            (CURRENT-ACL2-WORLD)
            (CURRENT-PACKAGE . "ACL2")
            (DEBUGGER-ENABLE)
            (DEFAXIOMS-OKP-CERT . T)
            (DISTRIBUTED-BOOKS-DIR)
            (DMRP)
            (EVISC-HITP-WITHOUT-IPRINT)
            (EVISCERATE-HIDE-TERMS)
            (FMT-HARD-RIGHT-MARGIN . 77)
            (FMT-SOFT-RIGHT-MARGIN . 65)
            (GAG-MODE)
            (GAG-STATE)
            (GAG-STATE-SAVED)
            (GLOBAL-ENABLED-STRUCTURE)
            (GSTACKP)
            (GUARD-CHECKING-ON . T)
            (HONS-ENABLED)
            (HONS-READ-P . T)
            (IN-LOCAL-FLG)
            (IN-PROVE-FLG)
            (IN-VERIFY-FLG)
            (INFIXP)
            (INHIBIT-OUTPUT-LST SUMMARY)
            (INHIBIT-OUTPUT-LST-STACK)
            (IPRINT-AR (:HEADER :DIMENSIONS (10001)
                                :MAXIMUM-LENGTH 40004
                                :DEFAULT NIL
                                :NAME IPRINT-AR
                                :ORDER :NONE)
                       (0 0))
            (IPRINT-HARD-BOUND . 10000)
            (IPRINT-SOFT-BOUND . 1000)
            (KEEP-TMP-FILES)
            (LAST-MAKE-EVENT-EXPANSION)
            (LD-LEVEL . 0)
            (LD-REDEFINITION-ACTION)
            (LD-SKIP-PROOFSP)
            (LOGIC-FNS-WITH-RAW-CODE MOD-EXPT HEADER SEARCH-FN STATE-P1
                                     AREF2 AREF1 MFC-ANCESTORS FGETPROP
                                     GETENV$ WORMHOLE1 ASET2 SGETPROP SETENV$
                                     GETPROPS COMPRESS1 TIME-LIMIT4-REACHED-P
                                     FMT-TO-COMMENT-WINDOW
                                     LEN MFC-CLAUSE CPU-CORE-COUNT
                                     NONNEGATIVE-INTEGER-QUOTIENT
                                     CHECK-PRINT-BASE RETRACT-WORLD
                                     ASET1 ARRAY1P BOOLE$ ARRAY2P STRIP-CDRS
                                     COMPRESS2 STRIP-CARS WORLDP WORMHOLE-P
                                     MFC-TYPE-ALIST MAY-NEED-SLASHES-FN
                                     FMT-TO-COMMENT-WINDOW!
                                     HAS-PROPSP HARD-ERROR
                                     ABORT! MFC-RDEPTH FLUSH-COMPRESS
                                     ALPHORDER EXTEND-WORLD USER-STOBJ-ALIST
                                     READ-ACL2-ORACLE UPDATE-USER-STOBJ-ALIST
                                     DECREMENT-BIG-CLOCK
                                     PUT-GLOBAL CLOSE-INPUT-CHANNEL
                                     MAKUNBOUND-GLOBAL OPEN-INPUT-CHANNEL-P1
                                     BOUNDP-GLOBAL1 GLOBAL-TABLE-CARS1
                                     EXTEND-T-STACK LIST-ALL-PACKAGE-NAMES
                                     CLOSE-OUTPUT-CHANNEL WRITE-BYTE$
                                     SHRINK-T-STACK ASET-32-BIT-INTEGER-STACK
                                     GET-GLOBAL 32-BIT-INTEGER-STACK-LENGTH1
                                     EXTEND-32-BIT-INTEGER-STACK ASET-T-STACK
                                     WITH-PROVER-TIME-LIMIT AREF-T-STACK
                                     READ-CHAR$ AREF-32-BIT-INTEGER-STACK
                                     OPEN-OUTPUT-CHANNEL-P1
                                     READ-OBJECT BIG-CLOCK-NEGATIVE-P
                                     PEEK-CHAR$ SHRINK-32-BIT-INTEGER-STACK
                                     READ-RUN-TIME READ-BYTE$ EC-CALL
                                     PROG2$ READ-IDATE TIME$ PRINT-OBJECT$
                                     T-STACK-LENGTH1 MUST-BE-EQUAL ZPF
                                     IDENTITY ENDP NTHCDR LAST REVAPPEND NULL
                                     BUTLAST STRING MEMBER NOT MOD PLUSP ATOM
                                     LISTP ZP FLOOR CEILING TRUNCATE ROUND
                                     REM REMOVE REMOVE-DUPLICATES LOGBITP
                                     ASH LOGCOUNT SIGNUM INTEGER-LENGTH
                                     EXPT SUBSETP SUBSTITUTE ZEROP
                                     MINUSP ODDP EVENP = /= MAX MIN CONJUGATE
                                     LOGANDC1 LOGANDC2 LOGNAND LOGNOR LOGNOT
                                     LOGORC1 LOGORC2 LOGTEST POSITION ABS
                                     STRING-EQUAL STRING< STRING> STRING<=
                                     STRING>= STRING-UPCASE STRING-DOWNCASE
                                     KEYWORDP EQ EQL CHAR SUBST SUBLIS
                                     ACONS ASSOC RASSOC NTH SUBSEQ LENGTH
                                     REVERSE ZIP STANDARD-CHAR-P ALPHA-CHAR-P
                                     UPPER-CASE-P LOWER-CASE-P CHAR< CHAR>
                                     CHAR<= CHAR>= CHAR-EQUAL CHAR-UPCASE
                                     CHAR-DOWNCASE HONS-READ-OBJECT
                                     AND-LIST OR-LIST RANDOM$)
            (MACROS-WITH-RAW-CODE MBE
                                  THEORY-INVARIANT SET-LET*-ABSTRACTIONP
                                  DEFAXIOM SET-BOGUS-MUTUAL-RECURSION-OK
                                  SET-RULER-EXTENDERS
                                  DELETE-INCLUDE-BOOK-DIR CERTIFY-BOOK
                                  PROGN! F-PUT-GLOBAL PUSH-UNTOUCHABLE
                                  SET-BACKCHAIN-LIMIT SET-DEFAULT-HINTS!
                                  DEFTHEORY PSTK VERIFY-GUARDS
                                  DEFCHOOSE SET-DEFAULT-BACKCHAIN-LIMIT
                                  SET-STATE-OK SET-IGNORE-OK
                                  SET-NON-LINEARP WITH-OUTPUT
                                  SET-COMPILE-FNS ADD-INCLUDE-BOOK-DIR
                                  CLEAR-PSTK ADD-CUSTOM-KEYWORD-HINT
                                  INITIAL-GSTACK ASSIGN-WORMHOLE-OUTPUT
                                  ACL2-UNWIND-PROTECT
                                  SET-WELL-FOUNDED-RELATION
                                  CATCH-TIME-LIMIT4 DEFUNS
                                  ADD-DEFAULT-HINTS! LOCAL ENCAPSULATE
                                  REMOVE-DEFAULT-HINTS! INCLUDE-BOOK
                                  PPROGN SET-ENFORCE-REDUNDANCY
                                  SET-IGNORE-DOC-STRING-ERROR LOGIC
                                  ER DEFLABEL MV-LET PROGRAM VALUE-TRIPLE
                                  SET-BODY COMP SET-BOGUS-DEFUN-HINTS-OK
                                  DMR-STOP DEFPKG SET-MEASURE-FUNCTION
                                  SET-INHIBIT-WARNINGS DEFTHM MV
                                  F-BIG-CLOCK-NEGATIVE-P RESET-PREHISTORY
                                  MUTUAL-RECURSION SET-REWRITE-STACK-LIMIT
                                  ADD-MATCH-FREE-OVERRIDE
                                  SET-INHIBIT-OUTPUT-LST
                                  SET-MATCH-FREE-DEFAULT
                                  THE-MV TABLE IN-ARITHMETIC-THEORY
                                  SET-CASE-SPLIT-LIMITATIONS
                                  SET-IRRELEVANT-FORMALS-OK
                                  REMOVE-UNTOUCHABLE
                                  IN-THEORY WITH-OUTPUT-FORCED
                                  DMR-START REWRITE-ENTRY
                                  SKIP-PROOFS F-BOUNDP-GLOBAL
                                  MAKE-EVENT SET-VERIFY-GUARDS-EAGERNESS
                                  WORMHOLE VERIFY-TERMINATION-BOOT-STRAP
                                  START-PROOF-TREE F-DECREMENT-BIG-CLOCK
                                  DEFSTOBJ DEFUND DEFTTAG
                                  DEFDOC PUSH-GFRAME DEFTHMD F-GET-GLOBAL
                                  SET-NU-REWRITER-MODE CAAR CADR
                                  CDAR CDDR CAAAR CAADR CADAR CADDR CDAAR
                                  CDADR CDDAR CDDDR CAAAAR CAAADR CAADAR
                                  CAADDR CADAAR CADADR CADDAR CADDDR
                                  CDAAAR CDAADR CDADAR CDADDR CDDAAR
                                  CDDADR CDDDAR CDDDDR REST MAKE-LIST LIST
                                  OR AND * LOGIOR LOGXOR LOGAND SEARCH
                                  LOGEQV CONCATENATE LET* DEFUN THE > <=
                                  >= + - / 1+ 1- PROGN DEFMACRO COND CASE
                                  LIST* APPEND DEFCONST IN-PACKAGE INTERN
                                  FIRST SECOND THIRD FOURTH FIFTH SIXTH
                                  SEVENTH EIGHTH NINTH TENTH DIGIT-CHAR-P
                                  UNMEMOIZE HONS-LET MEMOIZE-LET MEMOIZE
                                  DEFUNS-STD DEFTHM-STD DEFUN-STD POR
                                  PAND PLET PARGS TRACE! WITH-LIVE-STATE
                                  WITH-OUTPUT-OBJECT-CHANNEL-SHARING)
            (MAIN-TIMER . 0)
            (MAKE-EVENT-DEBUG)
            (MAKE-EVENT-DEBUG-DEPTH . 0)
            (MATCH-FREE-ERROR)
            (MORE-DOC-MAX-LINES . 45)
            (MORE-DOC-MIN-LINES . 35)
            (MORE-DOC-STATE)
            (MSWINDOWS-DRIVE)
            (PACKAGES-CREATED-BY-DEFPKG)
            (PARALLEL-EVALUATION-ENABLED)
            (PC-OUTPUT)
            (PPR-FLAT-RIGHT-MARGIN . 40)
            (PRINT-BASE . 10)
            (PRINT-CASE . :UPCASE)
            (PRINT-CIRCLE)
            (PRINT-CLAUSE-IDS)
            (PRINT-DOC-START-COLUMN . 15)
            (PRINT-ESCAPE . T)
            (PRINT-LENGTH)
            (PRINT-LEVEL)
            (PRINT-LINES)
            (PRINT-PRETTY)
            (PRINT-RADIX)
            (PRINT-READABLY)
            (PRINT-RIGHT-MARGIN)
            (PROGRAM-FNS-WITH-RAW-CODE
                 RELIEVE-HYP-SYNP
                 APPLY-ABBREVS-TO-LAMBDA-STACK1
                 GOOD-BYE-FN NTH-UPDATE-REWRITER
                 EV-W-LST SIMPLIFY-CLAUSE1
                 EV-REC-ACL2-UNWIND-PROTECT
                 ALLOCATE-FIXNUM-RANGE TRACE$-FN-GENERAL
                 EV-FNCALL! OPEN-TRACE-FILE-FN
                 SET-TRACE-EVISC-TUPLE EV-FNCALL-W
                 EV-REC SETUP-SIMPLIFY-CLAUSE-POT-LST1
                 SAVE-EXEC CW-GSTACK-FN
                 RECOMPRESS-GLOBAL-ENABLED-STRUCTURE EV-W
                 VERBOSE-PSTACK USER-STOBJ-ALIST-SAFE
                 COMP-FN FMT-PPR GET-MEMO
                 ACL2-RAW-EVAL PSTACK-FN DMR-START-FN
                 MEMO-EXIT MEMO-KEY1 SYS-CALL-STATUS
                 EV-FNCALL-META SET-DEBUGGER-ENABLE-FN
                 LD-LOOP PRINT-SUMMARY
                 EV EV-LST ALLEGRO-ALLOCATE-SLOWLY-FN
                 CERTIFY-BOOK-FN
                 TRANSLATE11-FLET-ALIST1 INCLUDE-BOOK-FN
                 FMT1 FLSZ SET-W PROVE-LOOP CHK-VIRGIN
                 W-OF-ANY-STATE PRINT-NEWLINE-FOR-TIME$
                 LAMBDA-ABSTRACT LD-FN-BODY UNTRANSLATE
                 LONGEST-COMMON-TAIL-LENGTH-REC
                 COMPILE-FUNCTION UNTRANSLATE-LST EV-SYNP
                 ADD-POLYS DMR-STOP-FN LD-PRINT-RESULTS
                 APPLY-ABBREVS-TO-LAMBDA-STACK
                 BREAK$ FLPR CLOSE-TRACE-FILE-FN
                 EV-FNCALL-REC SYS-CALL EV-FNCALL LD-FN0
                 LD-FN WRITE-EXPANSION-FILE LATCH-STOBJS1
                 CHK-PACKAGE-REINCARNATION-IMPORT-RESTRICTIONS
                 UNTRACE$-FN1 BDD-TOP
                 GC$-FN DEFSTOBJ-FIELD-FNS-RAW-DEFS
                 EXPANSION-ALIST-PKG-NAMES
                 TIMES-MOD-M31 PRINT-CALL-HISTORY
                 IPRINT-AR-AREF1 PROVE MAKE-EVENT-FN)
            (PROMPT-FUNCTION . DEFAULT-PRINT-PROMPT)
            (PROMPT-MEMO)
            (PROOF-TREE)
            (PROOF-TREE-BUFFER-WIDTH . 65)
            (PROOF-TREE-CTX)
            (PROOF-TREE-INDENT . "|  ")
            (PROOF-TREE-START-PRINTED)
            (PROOFS-CO .
                       ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (RAW-ARITY-ALIST)
            (RAW-PROOF-FORMAT)
            (REDO-FLAT-FAIL)
            (REDO-FLAT-SUCC)
            (REDUNDANT-WITH-RAW-CODE-OKP)
            (SAFE-MODE)
            (SAVED-OUTPUT-P)
            (SAVED-OUTPUT-REVERSED)
            (SAVED-OUTPUT-TOKEN-LST)
            (SHOW-CUSTOM-KEYWORD-HINT-EXPANSION)
            (SKIP-NOTIFY-ON-DEFTTAG)
            (SKIP-PROOFS-BY-SYSTEM)
            (SKIP-PROOFS-OKP-CERT . T)
            (SLOW-ARRAY-ACTION . :BREAK)
            (STANDARD-CO .
                         ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (STANDARD-OI .
                         ACL2-OUTPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
            (SUPPRESS-COMPILE)
            (TAINTED-OKP)
            (TEMP-TOUCHABLE-FNS)
            (TEMP-TOUCHABLE-VARS)
            (TERM-EVISC-TUPLE . :DEFAULT)
            (TIMER-ALIST)
            (TMP-DIR)
            (TRACE-CO .
                      ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
            (TRACE-LEVEL . 0)
            (TRACE-SPECS)
            (TRANSLATE-ERROR-DEPTH . -1)
            (TRIPLE-PRINT-PREFIX . " ")
            (TTAGS-ALLOWED . :ALL)
            (UNDONE-WORLDS-KILL-RING NIL NIL NIL)
            (USER-HOME-DIR)
            (WINDOW-INTERFACE-POSTLUDE
                 .
                 "#>\\>#<\\<e(acl2-window-postlude ?~sw ~xt ~xp)#>\\>")
            (WINDOW-INTERFACE-PRELUDE
                 .
                 "~%#<\\<e(acl2-window-prelude ?~sw ~xc)#>\\>#<\\<~sw")
            (WINDOW-INTERFACEP)
            (WORMHOLE-NAME)
            (WORMHOLE-OUTPUT)
            (WRITES-OKP . T))
           NIL NIL 4000000
           NIL NIL 1 NIL NIL NIL NIL NIL NIL)))
  (CONS
   OPEN-INPUT-CHANNELS
   (CONS
    OPEN-OUTPUT-CHANNELS
    (CONS
     GLOBAL-TABLE
     (CONS
      T-STACK
      (CONS
       32-BIT-INTEGER-STACK
       (CONS
        BIG-CLOCK
        (CONS
         IDATES
         (CONS
          ACL2-ORACLE
          (CONS
           FILE-CLOCK
           (CONS
            READABLE-FILES
            (CONS
               WRITTEN-FILES
               (CONS READ-FILES
                     (CONS WRITEABLE-FILES
                           (CONS LIST-ALL-PACKAGE-NAMES-LST
                                 (CONS USER-STOBJ-ALIST 'NIL)))))))))))))))))

(DEFUN COERCE-STATE-TO-OBJECT (X) X)

(DEFUN COERCE-OBJECT-TO-STATE (X) X)

(DEFUN GLOBAL-TABLE-CARS1 (STATE-STATE)
       (STRIP-CARS (GLOBAL-TABLE STATE-STATE)))

(DEFUN GLOBAL-TABLE-CARS (STATE-STATE) (GLOBAL-TABLE-CARS1 STATE-STATE))

(DEFUN BOUNDP-GLOBAL1 (X STATE-STATE)
       (IF (ASSOC X (GLOBAL-TABLE STATE-STATE))
           'T
           'NIL))

(DEFUN BOUNDP-GLOBAL (X STATE-STATE) (BOUNDP-GLOBAL1 X STATE-STATE))

(DEFUN DELETE-PAIR (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQ X (CAR (CAR L)))
               (CDR L)
               (CONS (CAR L)
                     (DELETE-PAIR X (CDR L))))))

(DEFUN MAKUNBOUND-GLOBAL (X STATE-STATE)
       (UPDATE-GLOBAL-TABLE (DELETE-PAIR X (GLOBAL-TABLE STATE-STATE))
                            STATE-STATE))

(DEFUN GET-GLOBAL (X STATE-STATE)
       (CDR (ASSOC X (GLOBAL-TABLE STATE-STATE))))

(DEFUN PUT-GLOBAL (KEY VALUE STATE-STATE)
       (UPDATE-GLOBAL-TABLE (ADD-PAIR KEY VALUE (GLOBAL-TABLE STATE-STATE))
                            STATE-STATE))

(DEFUN SYMBOL-DOUBLET-LISTP (LST)
       (IF (ATOM LST)
           (EQ LST 'NIL)
           (IF (CONSP (CAR LST))
               (IF (SYMBOLP (CAR (CAR LST)))
                   (IF (CONSP (CDR (CAR LST)))
                       (IF (NULL (CDR (CDR (CAR LST))))
                           (SYMBOL-DOUBLET-LISTP (CDR LST))
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN
 ALWAYS-BOUNDP-GLOBAL (X)
 (IF
  (ASSOC-EQ
   X
   '((ABBREV-EVISC-TUPLE . :DEFAULT)
     (ACCUMULATED-TTREE)
     (ACCUMULATED-WARNINGS)
     (ACL2-RAW-MODE-P)
     (ACL2-VERSION . "ACL2 Version 3.5")
     (AXIOMSP)
     (BDDNOTES)
     (CERTIFY-BOOK-DISABLEDP)
     (CERTIFY-BOOK-INFO)
     (CHECKPOINT-FORCED-GOALS)
     (CHECKPOINT-PROCESSORS ELIMINATE-DESTRUCTORS-CLAUSE
                            FERTILIZE-CLAUSE GENERALIZE-CLAUSE
                            ELIMINATE-IRRELEVANCE-CLAUSE
                            PUSH-CLAUSE :INDUCT)
     (CHECKPOINT-SUMMARY-LIMIT NIL . 3)
     (CONNECTED-BOOK-DIRECTORY)
     (CURRENT-ACL2-WORLD)
     (CURRENT-PACKAGE . "ACL2")
     (DEBUGGER-ENABLE)
     (DEFAXIOMS-OKP-CERT . T)
     (DISTRIBUTED-BOOKS-DIR)
     (DMRP)
     (EVISC-HITP-WITHOUT-IPRINT)
     (EVISCERATE-HIDE-TERMS)
     (FMT-HARD-RIGHT-MARGIN . 77)
     (FMT-SOFT-RIGHT-MARGIN . 65)
     (GAG-MODE)
     (GAG-STATE)
     (GAG-STATE-SAVED)
     (GLOBAL-ENABLED-STRUCTURE)
     (GSTACKP)
     (GUARD-CHECKING-ON . T)
     (HONS-ENABLED)
     (HONS-READ-P . T)
     (IN-LOCAL-FLG)
     (IN-PROVE-FLG)
     (IN-VERIFY-FLG)
     (INFIXP)
     (INHIBIT-OUTPUT-LST SUMMARY)
     (INHIBIT-OUTPUT-LST-STACK)
     (IPRINT-AR (:HEADER :DIMENSIONS (10001)
                         :MAXIMUM-LENGTH 40004
                         :DEFAULT NIL
                         :NAME IPRINT-AR
                         :ORDER :NONE)
                (0 0))
     (IPRINT-HARD-BOUND . 10000)
     (IPRINT-SOFT-BOUND . 1000)
     (KEEP-TMP-FILES)
     (LAST-MAKE-EVENT-EXPANSION)
     (LD-LEVEL . 0)
     (LD-REDEFINITION-ACTION)
     (LD-SKIP-PROOFSP)
     (LOGIC-FNS-WITH-RAW-CODE MOD-EXPT HEADER SEARCH-FN STATE-P1
                              AREF2 AREF1 MFC-ANCESTORS FGETPROP
                              GETENV$ WORMHOLE1 ASET2 SGETPROP SETENV$
                              GETPROPS COMPRESS1 TIME-LIMIT4-REACHED-P
                              FMT-TO-COMMENT-WINDOW
                              LEN MFC-CLAUSE CPU-CORE-COUNT
                              NONNEGATIVE-INTEGER-QUOTIENT
                              CHECK-PRINT-BASE RETRACT-WORLD
                              ASET1 ARRAY1P BOOLE$ ARRAY2P STRIP-CDRS
                              COMPRESS2 STRIP-CARS WORLDP WORMHOLE-P
                              MFC-TYPE-ALIST MAY-NEED-SLASHES-FN
                              FMT-TO-COMMENT-WINDOW!
                              HAS-PROPSP HARD-ERROR
                              ABORT! MFC-RDEPTH FLUSH-COMPRESS
                              ALPHORDER EXTEND-WORLD USER-STOBJ-ALIST
                              READ-ACL2-ORACLE UPDATE-USER-STOBJ-ALIST
                              DECREMENT-BIG-CLOCK
                              PUT-GLOBAL CLOSE-INPUT-CHANNEL
                              MAKUNBOUND-GLOBAL OPEN-INPUT-CHANNEL-P1
                              BOUNDP-GLOBAL1 GLOBAL-TABLE-CARS1
                              EXTEND-T-STACK LIST-ALL-PACKAGE-NAMES
                              CLOSE-OUTPUT-CHANNEL WRITE-BYTE$
                              SHRINK-T-STACK ASET-32-BIT-INTEGER-STACK
                              GET-GLOBAL 32-BIT-INTEGER-STACK-LENGTH1
                              EXTEND-32-BIT-INTEGER-STACK ASET-T-STACK
                              WITH-PROVER-TIME-LIMIT AREF-T-STACK
                              READ-CHAR$ AREF-32-BIT-INTEGER-STACK
                              OPEN-OUTPUT-CHANNEL-P1
                              READ-OBJECT BIG-CLOCK-NEGATIVE-P
                              PEEK-CHAR$ SHRINK-32-BIT-INTEGER-STACK
                              READ-RUN-TIME READ-BYTE$ EC-CALL
                              PROG2$ READ-IDATE TIME$ PRINT-OBJECT$
                              T-STACK-LENGTH1 MUST-BE-EQUAL ZPF
                              IDENTITY ENDP NTHCDR LAST REVAPPEND NULL
                              BUTLAST STRING MEMBER NOT MOD PLUSP ATOM
                              LISTP ZP FLOOR CEILING TRUNCATE ROUND
                              REM REMOVE REMOVE-DUPLICATES LOGBITP
                              ASH LOGCOUNT SIGNUM INTEGER-LENGTH
                              EXPT SUBSETP SUBSTITUTE ZEROP
                              MINUSP ODDP EVENP = /= MAX MIN CONJUGATE
                              LOGANDC1 LOGANDC2 LOGNAND LOGNOR LOGNOT
                              LOGORC1 LOGORC2 LOGTEST POSITION ABS
                              STRING-EQUAL STRING< STRING> STRING<=
                              STRING>= STRING-UPCASE STRING-DOWNCASE
                              KEYWORDP EQ EQL CHAR SUBST SUBLIS
                              ACONS ASSOC RASSOC NTH SUBSEQ LENGTH
                              REVERSE ZIP STANDARD-CHAR-P ALPHA-CHAR-P
                              UPPER-CASE-P LOWER-CASE-P CHAR< CHAR>
                              CHAR<= CHAR>= CHAR-EQUAL CHAR-UPCASE
                              CHAR-DOWNCASE HONS-READ-OBJECT
                              AND-LIST OR-LIST RANDOM$)
     (MACROS-WITH-RAW-CODE MBE
                           THEORY-INVARIANT SET-LET*-ABSTRACTIONP
                           DEFAXIOM SET-BOGUS-MUTUAL-RECURSION-OK
                           SET-RULER-EXTENDERS
                           DELETE-INCLUDE-BOOK-DIR CERTIFY-BOOK
                           PROGN! F-PUT-GLOBAL PUSH-UNTOUCHABLE
                           SET-BACKCHAIN-LIMIT SET-DEFAULT-HINTS!
                           DEFTHEORY PSTK VERIFY-GUARDS
                           DEFCHOOSE SET-DEFAULT-BACKCHAIN-LIMIT
                           SET-STATE-OK SET-IGNORE-OK
                           SET-NON-LINEARP WITH-OUTPUT
                           SET-COMPILE-FNS ADD-INCLUDE-BOOK-DIR
                           CLEAR-PSTK ADD-CUSTOM-KEYWORD-HINT
                           INITIAL-GSTACK ASSIGN-WORMHOLE-OUTPUT
                           ACL2-UNWIND-PROTECT
                           SET-WELL-FOUNDED-RELATION
                           CATCH-TIME-LIMIT4 DEFUNS
                           ADD-DEFAULT-HINTS! LOCAL ENCAPSULATE
                           REMOVE-DEFAULT-HINTS! INCLUDE-BOOK
                           PPROGN SET-ENFORCE-REDUNDANCY
                           SET-IGNORE-DOC-STRING-ERROR LOGIC
                           ER DEFLABEL MV-LET PROGRAM VALUE-TRIPLE
                           SET-BODY COMP SET-BOGUS-DEFUN-HINTS-OK
                           DMR-STOP DEFPKG SET-MEASURE-FUNCTION
                           SET-INHIBIT-WARNINGS DEFTHM MV
                           F-BIG-CLOCK-NEGATIVE-P RESET-PREHISTORY
                           MUTUAL-RECURSION SET-REWRITE-STACK-LIMIT
                           ADD-MATCH-FREE-OVERRIDE
                           SET-INHIBIT-OUTPUT-LST
                           SET-MATCH-FREE-DEFAULT
                           THE-MV TABLE IN-ARITHMETIC-THEORY
                           SET-CASE-SPLIT-LIMITATIONS
                           SET-IRRELEVANT-FORMALS-OK
                           REMOVE-UNTOUCHABLE
                           IN-THEORY WITH-OUTPUT-FORCED
                           DMR-START REWRITE-ENTRY
                           SKIP-PROOFS F-BOUNDP-GLOBAL
                           MAKE-EVENT SET-VERIFY-GUARDS-EAGERNESS
                           WORMHOLE VERIFY-TERMINATION-BOOT-STRAP
                           START-PROOF-TREE F-DECREMENT-BIG-CLOCK
                           DEFSTOBJ DEFUND DEFTTAG
                           DEFDOC PUSH-GFRAME DEFTHMD F-GET-GLOBAL
                           SET-NU-REWRITER-MODE CAAR CADR
                           CDAR CDDR CAAAR CAADR CADAR CADDR CDAAR
                           CDADR CDDAR CDDDR CAAAAR CAAADR CAADAR
                           CAADDR CADAAR CADADR CADDAR CADDDR
                           CDAAAR CDAADR CDADAR CDADDR CDDAAR
                           CDDADR CDDDAR CDDDDR REST MAKE-LIST LIST
                           OR AND * LOGIOR LOGXOR LOGAND SEARCH
                           LOGEQV CONCATENATE LET* DEFUN THE > <=
                           >= + - / 1+ 1- PROGN DEFMACRO COND CASE
                           LIST* APPEND DEFCONST IN-PACKAGE INTERN
                           FIRST SECOND THIRD FOURTH FIFTH SIXTH
                           SEVENTH EIGHTH NINTH TENTH DIGIT-CHAR-P
                           UNMEMOIZE HONS-LET MEMOIZE-LET MEMOIZE
                           DEFUNS-STD DEFTHM-STD DEFUN-STD POR
                           PAND PLET PARGS TRACE! WITH-LIVE-STATE
                           WITH-OUTPUT-OBJECT-CHANNEL-SHARING)
     (MAIN-TIMER . 0)
     (MAKE-EVENT-DEBUG)
     (MAKE-EVENT-DEBUG-DEPTH . 0)
     (MATCH-FREE-ERROR)
     (MORE-DOC-MAX-LINES . 45)
     (MORE-DOC-MIN-LINES . 35)
     (MORE-DOC-STATE)
     (MSWINDOWS-DRIVE)
     (PACKAGES-CREATED-BY-DEFPKG)
     (PARALLEL-EVALUATION-ENABLED)
     (PC-OUTPUT)
     (PPR-FLAT-RIGHT-MARGIN . 40)
     (PRINT-BASE . 10)
     (PRINT-CASE . :UPCASE)
     (PRINT-CIRCLE)
     (PRINT-CLAUSE-IDS)
     (PRINT-DOC-START-COLUMN . 15)
     (PRINT-ESCAPE . T)
     (PRINT-LENGTH)
     (PRINT-LEVEL)
     (PRINT-LINES)
     (PRINT-PRETTY)
     (PRINT-RADIX)
     (PRINT-READABLY)
     (PRINT-RIGHT-MARGIN)
     (PROGRAM-FNS-WITH-RAW-CODE RELIEVE-HYP-SYNP
                                APPLY-ABBREVS-TO-LAMBDA-STACK1
                                GOOD-BYE-FN NTH-UPDATE-REWRITER
                                EV-W-LST SIMPLIFY-CLAUSE1
                                EV-REC-ACL2-UNWIND-PROTECT
                                ALLOCATE-FIXNUM-RANGE TRACE$-FN-GENERAL
                                EV-FNCALL! OPEN-TRACE-FILE-FN
                                SET-TRACE-EVISC-TUPLE EV-FNCALL-W
                                EV-REC SETUP-SIMPLIFY-CLAUSE-POT-LST1
                                SAVE-EXEC CW-GSTACK-FN
                                RECOMPRESS-GLOBAL-ENABLED-STRUCTURE EV-W
                                VERBOSE-PSTACK USER-STOBJ-ALIST-SAFE
                                COMP-FN FMT-PPR GET-MEMO
                                ACL2-RAW-EVAL PSTACK-FN DMR-START-FN
                                MEMO-EXIT MEMO-KEY1 SYS-CALL-STATUS
                                EV-FNCALL-META SET-DEBUGGER-ENABLE-FN
                                LD-LOOP PRINT-SUMMARY
                                EV EV-LST ALLEGRO-ALLOCATE-SLOWLY-FN
                                CERTIFY-BOOK-FN
                                TRANSLATE11-FLET-ALIST1 INCLUDE-BOOK-FN
                                FMT1 FLSZ SET-W PROVE-LOOP CHK-VIRGIN
                                W-OF-ANY-STATE PRINT-NEWLINE-FOR-TIME$
                                LAMBDA-ABSTRACT LD-FN-BODY UNTRANSLATE
                                LONGEST-COMMON-TAIL-LENGTH-REC
                                COMPILE-FUNCTION UNTRANSLATE-LST EV-SYNP
                                ADD-POLYS DMR-STOP-FN LD-PRINT-RESULTS
                                APPLY-ABBREVS-TO-LAMBDA-STACK
                                BREAK$ FLPR CLOSE-TRACE-FILE-FN
                                EV-FNCALL-REC SYS-CALL EV-FNCALL LD-FN0
                                LD-FN WRITE-EXPANSION-FILE LATCH-STOBJS1
                                CHK-PACKAGE-REINCARNATION-IMPORT-RESTRICTIONS
                                UNTRACE$-FN1 BDD-TOP
                                GC$-FN DEFSTOBJ-FIELD-FNS-RAW-DEFS
                                EXPANSION-ALIST-PKG-NAMES
                                TIMES-MOD-M31 PRINT-CALL-HISTORY
                                IPRINT-AR-AREF1 PROVE MAKE-EVENT-FN)
     (PROMPT-FUNCTION . DEFAULT-PRINT-PROMPT)
     (PROMPT-MEMO)
     (PROOF-TREE)
     (PROOF-TREE-BUFFER-WIDTH . 65)
     (PROOF-TREE-CTX)
     (PROOF-TREE-INDENT . "|  ")
     (PROOF-TREE-START-PRINTED)
     (PROOFS-CO .
                ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (RAW-ARITY-ALIST)
     (RAW-PROOF-FORMAT)
     (REDO-FLAT-FAIL)
     (REDO-FLAT-SUCC)
     (REDUNDANT-WITH-RAW-CODE-OKP)
     (SAFE-MODE)
     (SAVED-OUTPUT-P)
     (SAVED-OUTPUT-REVERSED)
     (SAVED-OUTPUT-TOKEN-LST)
     (SHOW-CUSTOM-KEYWORD-HINT-EXPANSION)
     (SKIP-NOTIFY-ON-DEFTTAG)
     (SKIP-PROOFS-BY-SYSTEM)
     (SKIP-PROOFS-OKP-CERT . T)
     (SLOW-ARRAY-ACTION . :BREAK)
     (STANDARD-CO .
                  ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (STANDARD-OI .
                  ACL2-OUTPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
     (SUPPRESS-COMPILE)
     (TAINTED-OKP)
     (TEMP-TOUCHABLE-FNS)
     (TEMP-TOUCHABLE-VARS)
     (TERM-EVISC-TUPLE . :DEFAULT)
     (TIMER-ALIST)
     (TMP-DIR)
     (TRACE-CO .
               ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (TRACE-LEVEL . 0)
     (TRACE-SPECS)
     (TRANSLATE-ERROR-DEPTH . -1)
     (TRIPLE-PRINT-PREFIX . " ")
     (TTAGS-ALLOWED . :ALL)
     (UNDONE-WORLDS-KILL-RING NIL NIL NIL)
     (USER-HOME-DIR)
     (WINDOW-INTERFACE-POSTLUDE
          .
          "#>\\>#<\\<e(acl2-window-postlude ?~sw ~xt ~xp)#>\\>")
     (WINDOW-INTERFACE-PRELUDE
          .
          "~%#<\\<e(acl2-window-prelude ?~sw ~xc)#>\\>#<\\<~sw")
     (WINDOW-INTERFACEP)
     (WORMHOLE-NAME)
     (WORMHOLE-OUTPUT)
     (WRITES-OKP . T)))
  (ASSOC-EQ
   X
   '((ABBREV-EVISC-TUPLE . :DEFAULT)
     (ACCUMULATED-TTREE)
     (ACCUMULATED-WARNINGS)
     (ACL2-RAW-MODE-P)
     (ACL2-VERSION . "ACL2 Version 3.5")
     (AXIOMSP)
     (BDDNOTES)
     (CERTIFY-BOOK-DISABLEDP)
     (CERTIFY-BOOK-INFO)
     (CHECKPOINT-FORCED-GOALS)
     (CHECKPOINT-PROCESSORS ELIMINATE-DESTRUCTORS-CLAUSE
                            FERTILIZE-CLAUSE GENERALIZE-CLAUSE
                            ELIMINATE-IRRELEVANCE-CLAUSE
                            PUSH-CLAUSE :INDUCT)
     (CHECKPOINT-SUMMARY-LIMIT NIL . 3)
     (CONNECTED-BOOK-DIRECTORY)
     (CURRENT-ACL2-WORLD)
     (CURRENT-PACKAGE . "ACL2")
     (DEBUGGER-ENABLE)
     (DEFAXIOMS-OKP-CERT . T)
     (DISTRIBUTED-BOOKS-DIR)
     (DMRP)
     (EVISC-HITP-WITHOUT-IPRINT)
     (EVISCERATE-HIDE-TERMS)
     (FMT-HARD-RIGHT-MARGIN . 77)
     (FMT-SOFT-RIGHT-MARGIN . 65)
     (GAG-MODE)
     (GAG-STATE)
     (GAG-STATE-SAVED)
     (GLOBAL-ENABLED-STRUCTURE)
     (GSTACKP)
     (GUARD-CHECKING-ON . T)
     (HONS-ENABLED)
     (HONS-READ-P . T)
     (IN-LOCAL-FLG)
     (IN-PROVE-FLG)
     (IN-VERIFY-FLG)
     (INFIXP)
     (INHIBIT-OUTPUT-LST SUMMARY)
     (INHIBIT-OUTPUT-LST-STACK)
     (IPRINT-AR (:HEADER :DIMENSIONS (10001)
                         :MAXIMUM-LENGTH 40004
                         :DEFAULT NIL
                         :NAME IPRINT-AR
                         :ORDER :NONE)
                (0 0))
     (IPRINT-HARD-BOUND . 10000)
     (IPRINT-SOFT-BOUND . 1000)
     (KEEP-TMP-FILES)
     (LAST-MAKE-EVENT-EXPANSION)
     (LD-LEVEL . 0)
     (LD-REDEFINITION-ACTION)
     (LD-SKIP-PROOFSP)
     (LOGIC-FNS-WITH-RAW-CODE MOD-EXPT HEADER SEARCH-FN STATE-P1
                              AREF2 AREF1 MFC-ANCESTORS FGETPROP
                              GETENV$ WORMHOLE1 ASET2 SGETPROP SETENV$
                              GETPROPS COMPRESS1 TIME-LIMIT4-REACHED-P
                              FMT-TO-COMMENT-WINDOW
                              LEN MFC-CLAUSE CPU-CORE-COUNT
                              NONNEGATIVE-INTEGER-QUOTIENT
                              CHECK-PRINT-BASE RETRACT-WORLD
                              ASET1 ARRAY1P BOOLE$ ARRAY2P STRIP-CDRS
                              COMPRESS2 STRIP-CARS WORLDP WORMHOLE-P
                              MFC-TYPE-ALIST MAY-NEED-SLASHES-FN
                              FMT-TO-COMMENT-WINDOW!
                              HAS-PROPSP HARD-ERROR
                              ABORT! MFC-RDEPTH FLUSH-COMPRESS
                              ALPHORDER EXTEND-WORLD USER-STOBJ-ALIST
                              READ-ACL2-ORACLE UPDATE-USER-STOBJ-ALIST
                              DECREMENT-BIG-CLOCK
                              PUT-GLOBAL CLOSE-INPUT-CHANNEL
                              MAKUNBOUND-GLOBAL OPEN-INPUT-CHANNEL-P1
                              BOUNDP-GLOBAL1 GLOBAL-TABLE-CARS1
                              EXTEND-T-STACK LIST-ALL-PACKAGE-NAMES
                              CLOSE-OUTPUT-CHANNEL WRITE-BYTE$
                              SHRINK-T-STACK ASET-32-BIT-INTEGER-STACK
                              GET-GLOBAL 32-BIT-INTEGER-STACK-LENGTH1
                              EXTEND-32-BIT-INTEGER-STACK ASET-T-STACK
                              WITH-PROVER-TIME-LIMIT AREF-T-STACK
                              READ-CHAR$ AREF-32-BIT-INTEGER-STACK
                              OPEN-OUTPUT-CHANNEL-P1
                              READ-OBJECT BIG-CLOCK-NEGATIVE-P
                              PEEK-CHAR$ SHRINK-32-BIT-INTEGER-STACK
                              READ-RUN-TIME READ-BYTE$ EC-CALL
                              PROG2$ READ-IDATE TIME$ PRINT-OBJECT$
                              T-STACK-LENGTH1 MUST-BE-EQUAL ZPF
                              IDENTITY ENDP NTHCDR LAST REVAPPEND NULL
                              BUTLAST STRING MEMBER NOT MOD PLUSP ATOM
                              LISTP ZP FLOOR CEILING TRUNCATE ROUND
                              REM REMOVE REMOVE-DUPLICATES LOGBITP
                              ASH LOGCOUNT SIGNUM INTEGER-LENGTH
                              EXPT SUBSETP SUBSTITUTE ZEROP
                              MINUSP ODDP EVENP = /= MAX MIN CONJUGATE
                              LOGANDC1 LOGANDC2 LOGNAND LOGNOR LOGNOT
                              LOGORC1 LOGORC2 LOGTEST POSITION ABS
                              STRING-EQUAL STRING< STRING> STRING<=
                              STRING>= STRING-UPCASE STRING-DOWNCASE
                              KEYWORDP EQ EQL CHAR SUBST SUBLIS
                              ACONS ASSOC RASSOC NTH SUBSEQ LENGTH
                              REVERSE ZIP STANDARD-CHAR-P ALPHA-CHAR-P
                              UPPER-CASE-P LOWER-CASE-P CHAR< CHAR>
                              CHAR<= CHAR>= CHAR-EQUAL CHAR-UPCASE
                              CHAR-DOWNCASE HONS-READ-OBJECT
                              AND-LIST OR-LIST RANDOM$)
     (MACROS-WITH-RAW-CODE MBE
                           THEORY-INVARIANT SET-LET*-ABSTRACTIONP
                           DEFAXIOM SET-BOGUS-MUTUAL-RECURSION-OK
                           SET-RULER-EXTENDERS
                           DELETE-INCLUDE-BOOK-DIR CERTIFY-BOOK
                           PROGN! F-PUT-GLOBAL PUSH-UNTOUCHABLE
                           SET-BACKCHAIN-LIMIT SET-DEFAULT-HINTS!
                           DEFTHEORY PSTK VERIFY-GUARDS
                           DEFCHOOSE SET-DEFAULT-BACKCHAIN-LIMIT
                           SET-STATE-OK SET-IGNORE-OK
                           SET-NON-LINEARP WITH-OUTPUT
                           SET-COMPILE-FNS ADD-INCLUDE-BOOK-DIR
                           CLEAR-PSTK ADD-CUSTOM-KEYWORD-HINT
                           INITIAL-GSTACK ASSIGN-WORMHOLE-OUTPUT
                           ACL2-UNWIND-PROTECT
                           SET-WELL-FOUNDED-RELATION
                           CATCH-TIME-LIMIT4 DEFUNS
                           ADD-DEFAULT-HINTS! LOCAL ENCAPSULATE
                           REMOVE-DEFAULT-HINTS! INCLUDE-BOOK
                           PPROGN SET-ENFORCE-REDUNDANCY
                           SET-IGNORE-DOC-STRING-ERROR LOGIC
                           ER DEFLABEL MV-LET PROGRAM VALUE-TRIPLE
                           SET-BODY COMP SET-BOGUS-DEFUN-HINTS-OK
                           DMR-STOP DEFPKG SET-MEASURE-FUNCTION
                           SET-INHIBIT-WARNINGS DEFTHM MV
                           F-BIG-CLOCK-NEGATIVE-P RESET-PREHISTORY
                           MUTUAL-RECURSION SET-REWRITE-STACK-LIMIT
                           ADD-MATCH-FREE-OVERRIDE
                           SET-INHIBIT-OUTPUT-LST
                           SET-MATCH-FREE-DEFAULT
                           THE-MV TABLE IN-ARITHMETIC-THEORY
                           SET-CASE-SPLIT-LIMITATIONS
                           SET-IRRELEVANT-FORMALS-OK
                           REMOVE-UNTOUCHABLE
                           IN-THEORY WITH-OUTPUT-FORCED
                           DMR-START REWRITE-ENTRY
                           SKIP-PROOFS F-BOUNDP-GLOBAL
                           MAKE-EVENT SET-VERIFY-GUARDS-EAGERNESS
                           WORMHOLE VERIFY-TERMINATION-BOOT-STRAP
                           START-PROOF-TREE F-DECREMENT-BIG-CLOCK
                           DEFSTOBJ DEFUND DEFTTAG
                           DEFDOC PUSH-GFRAME DEFTHMD F-GET-GLOBAL
                           SET-NU-REWRITER-MODE CAAR CADR
                           CDAR CDDR CAAAR CAADR CADAR CADDR CDAAR
                           CDADR CDDAR CDDDR CAAAAR CAAADR CAADAR
                           CAADDR CADAAR CADADR CADDAR CADDDR
                           CDAAAR CDAADR CDADAR CDADDR CDDAAR
                           CDDADR CDDDAR CDDDDR REST MAKE-LIST LIST
                           OR AND * LOGIOR LOGXOR LOGAND SEARCH
                           LOGEQV CONCATENATE LET* DEFUN THE > <=
                           >= + - / 1+ 1- PROGN DEFMACRO COND CASE
                           LIST* APPEND DEFCONST IN-PACKAGE INTERN
                           FIRST SECOND THIRD FOURTH FIFTH SIXTH
                           SEVENTH EIGHTH NINTH TENTH DIGIT-CHAR-P
                           UNMEMOIZE HONS-LET MEMOIZE-LET MEMOIZE
                           DEFUNS-STD DEFTHM-STD DEFUN-STD POR
                           PAND PLET PARGS TRACE! WITH-LIVE-STATE
                           WITH-OUTPUT-OBJECT-CHANNEL-SHARING)
     (MAIN-TIMER . 0)
     (MAKE-EVENT-DEBUG)
     (MAKE-EVENT-DEBUG-DEPTH . 0)
     (MATCH-FREE-ERROR)
     (MORE-DOC-MAX-LINES . 45)
     (MORE-DOC-MIN-LINES . 35)
     (MORE-DOC-STATE)
     (MSWINDOWS-DRIVE)
     (PACKAGES-CREATED-BY-DEFPKG)
     (PARALLEL-EVALUATION-ENABLED)
     (PC-OUTPUT)
     (PPR-FLAT-RIGHT-MARGIN . 40)
     (PRINT-BASE . 10)
     (PRINT-CASE . :UPCASE)
     (PRINT-CIRCLE)
     (PRINT-CLAUSE-IDS)
     (PRINT-DOC-START-COLUMN . 15)
     (PRINT-ESCAPE . T)
     (PRINT-LENGTH)
     (PRINT-LEVEL)
     (PRINT-LINES)
     (PRINT-PRETTY)
     (PRINT-RADIX)
     (PRINT-READABLY)
     (PRINT-RIGHT-MARGIN)
     (PROGRAM-FNS-WITH-RAW-CODE RELIEVE-HYP-SYNP
                                APPLY-ABBREVS-TO-LAMBDA-STACK1
                                GOOD-BYE-FN NTH-UPDATE-REWRITER
                                EV-W-LST SIMPLIFY-CLAUSE1
                                EV-REC-ACL2-UNWIND-PROTECT
                                ALLOCATE-FIXNUM-RANGE TRACE$-FN-GENERAL
                                EV-FNCALL! OPEN-TRACE-FILE-FN
                                SET-TRACE-EVISC-TUPLE EV-FNCALL-W
                                EV-REC SETUP-SIMPLIFY-CLAUSE-POT-LST1
                                SAVE-EXEC CW-GSTACK-FN
                                RECOMPRESS-GLOBAL-ENABLED-STRUCTURE EV-W
                                VERBOSE-PSTACK USER-STOBJ-ALIST-SAFE
                                COMP-FN FMT-PPR GET-MEMO
                                ACL2-RAW-EVAL PSTACK-FN DMR-START-FN
                                MEMO-EXIT MEMO-KEY1 SYS-CALL-STATUS
                                EV-FNCALL-META SET-DEBUGGER-ENABLE-FN
                                LD-LOOP PRINT-SUMMARY
                                EV EV-LST ALLEGRO-ALLOCATE-SLOWLY-FN
                                CERTIFY-BOOK-FN
                                TRANSLATE11-FLET-ALIST1 INCLUDE-BOOK-FN
                                FMT1 FLSZ SET-W PROVE-LOOP CHK-VIRGIN
                                W-OF-ANY-STATE PRINT-NEWLINE-FOR-TIME$
                                LAMBDA-ABSTRACT LD-FN-BODY UNTRANSLATE
                                LONGEST-COMMON-TAIL-LENGTH-REC
                                COMPILE-FUNCTION UNTRANSLATE-LST EV-SYNP
                                ADD-POLYS DMR-STOP-FN LD-PRINT-RESULTS
                                APPLY-ABBREVS-TO-LAMBDA-STACK
                                BREAK$ FLPR CLOSE-TRACE-FILE-FN
                                EV-FNCALL-REC SYS-CALL EV-FNCALL LD-FN0
                                LD-FN WRITE-EXPANSION-FILE LATCH-STOBJS1
                                CHK-PACKAGE-REINCARNATION-IMPORT-RESTRICTIONS
                                UNTRACE$-FN1 BDD-TOP
                                GC$-FN DEFSTOBJ-FIELD-FNS-RAW-DEFS
                                EXPANSION-ALIST-PKG-NAMES
                                TIMES-MOD-M31 PRINT-CALL-HISTORY
                                IPRINT-AR-AREF1 PROVE MAKE-EVENT-FN)
     (PROMPT-FUNCTION . DEFAULT-PRINT-PROMPT)
     (PROMPT-MEMO)
     (PROOF-TREE)
     (PROOF-TREE-BUFFER-WIDTH . 65)
     (PROOF-TREE-CTX)
     (PROOF-TREE-INDENT . "|  ")
     (PROOF-TREE-START-PRINTED)
     (PROOFS-CO .
                ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (RAW-ARITY-ALIST)
     (RAW-PROOF-FORMAT)
     (REDO-FLAT-FAIL)
     (REDO-FLAT-SUCC)
     (REDUNDANT-WITH-RAW-CODE-OKP)
     (SAFE-MODE)
     (SAVED-OUTPUT-P)
     (SAVED-OUTPUT-REVERSED)
     (SAVED-OUTPUT-TOKEN-LST)
     (SHOW-CUSTOM-KEYWORD-HINT-EXPANSION)
     (SKIP-NOTIFY-ON-DEFTTAG)
     (SKIP-PROOFS-BY-SYSTEM)
     (SKIP-PROOFS-OKP-CERT . T)
     (SLOW-ARRAY-ACTION . :BREAK)
     (STANDARD-CO .
                  ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (STANDARD-OI .
                  ACL2-OUTPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
     (SUPPRESS-COMPILE)
     (TAINTED-OKP)
     (TEMP-TOUCHABLE-FNS)
     (TEMP-TOUCHABLE-VARS)
     (TERM-EVISC-TUPLE . :DEFAULT)
     (TIMER-ALIST)
     (TMP-DIR)
     (TRACE-CO .
               ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (TRACE-LEVEL . 0)
     (TRACE-SPECS)
     (TRANSLATE-ERROR-DEPTH . -1)
     (TRIPLE-PRINT-PREFIX . " ")
     (TTAGS-ALLOWED . :ALL)
     (UNDONE-WORLDS-KILL-RING NIL NIL NIL)
     (USER-HOME-DIR)
     (WINDOW-INTERFACE-POSTLUDE
          .
          "#>\\>#<\\<e(acl2-window-postlude ?~sw ~xt ~xp)#>\\>")
     (WINDOW-INTERFACE-PRELUDE
          .
          "~%#<\\<e(acl2-window-prelude ?~sw ~xc)#>\\>#<\\<~sw")
     (WINDOW-INTERFACEP)
     (WORMHOLE-NAME)
     (WORMHOLE-OUTPUT)
     (WRITES-OKP . T)))
  (ASSOC-EQ
   X
   '((STANDARD-OI .
                  ACL2-INPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
     (STANDARD-CO .
                  ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (PROOFS-CO .
                ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
     (LD-SKIP-PROOFSP)
     (LD-REDEFINITION-ACTION)
     (LD-PROMPT . T)
     (LD-KEYWORD-ALIASES)
     (LD-PRE-EVAL-FILTER . :ALL)
     (LD-PRE-EVAL-PRINT)
     (LD-POST-EVAL-PRINT . :COMMAND-CONVENTIONS)
     (LD-EVISC-TUPLE)
     (LD-ERROR-TRIPLES . T)
     (LD-ERROR-ACTION . :CONTINUE)
     (LD-QUERY-CONTROL-ALIST)
     (LD-VERBOSE
      .
      "~sv.  Level ~Fl.  Cbd ~xc.~|Distributed books ~
                   directory ~xb.~|Type :help for help.~%Type (good-bye) to ~
                   quit completely out of ACL2.~|~%")))))

(DEFUN STATE-GLOBAL-LET*-BINDINGS-P (LST)
       (IF (ATOM LST)
           (EQ LST 'NIL)
           (IF (CONSP (CAR LST))
               (IF (SYMBOLP (CAR (CAR LST)))
                   (IF (CONSP (CDR (CAR LST)))
                       (IF (IF (NULL (CDR (CDR (CAR LST))))
                               (NULL (CDR (CDR (CAR LST))))
                               (IF (CONSP (CDR (CDR (CAR LST))))
                                   (IF (SYMBOLP (CAR (CDR (CDR (CAR LST)))))
                                       (NULL (CDR (CDR (CDR (CAR LST)))))
                                       'NIL)
                                   'NIL))
                           (STATE-GLOBAL-LET*-BINDINGS-P (CDR LST))
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN
 STATE-GLOBAL-LET*-GET-GLOBALS (BINDINGS)
 (IF
  (ENDP BINDINGS)
  'NIL
  (CONS
   (IF
    (ALWAYS-BOUNDP-GLOBAL (CAR (CAR BINDINGS)))
    (CONS 'LIST
          (CONS (CONS 'F-GET-GLOBAL
                      (CONS (CONS 'QUOTE
                                  (CONS (CAR (CAR BINDINGS)) 'NIL))
                            (CONS 'STATE 'NIL)))
                'NIL))
    (CONS
     'IF
     (CONS
        (CONS 'F-BOUNDP-GLOBAL
              (CONS (CONS 'QUOTE
                          (CONS (CAR (CAR BINDINGS)) 'NIL))
                    (CONS 'STATE 'NIL)))
        (CONS (CONS 'LIST
                    (CONS (CONS 'F-GET-GLOBAL
                                (CONS (CONS 'QUOTE
                                            (CONS (CAR (CAR BINDINGS)) 'NIL))
                                      (CONS 'STATE 'NIL)))
                          'NIL))
              (CONS 'NIL 'NIL)))))
   (STATE-GLOBAL-LET*-GET-GLOBALS (CDR BINDINGS)))))

(DEFUN
 STATE-GLOBAL-LET*-PUT-GLOBALS (BINDINGS)
 (IF
  (ENDP BINDINGS)
  'NIL
  (CONS
   ((LAMBDA
     (VAL-FORM BINDINGS)
     (IF
      (CDR (CDR (CAR BINDINGS)))
      (CONS
       'IF
       (CONS
        (CONS 'F-BOUNDP-GLOBAL
              (CONS (CONS 'QUOTE
                          (CONS (CAR (CAR BINDINGS)) 'NIL))
                    (CONS 'STATE 'NIL)))
        (CONS
         (CONS (CAR (CDR (CDR (CAR BINDINGS))))
               (CONS VAL-FORM (CONS 'STATE 'NIL)))
         (CONS
          (CONS
           'PROG2$
           (CONS
            (CONS
             'ER
             (CONS
              'HARD
              (CONS
               (CONS 'QUOTE
                     (CONS 'STATE-GLOBAL-LET* 'NIL))
               (CONS
                '"It is illegal to bind an unbound variable ~
                                   in state-global-let*, in this case, ~x0, ~
                                   when a setter function is supplied."
                (CONS (CONS 'QUOTE
                            (CONS (CAR (CAR BINDINGS)) 'NIL))
                      'NIL)))))
            (CONS 'STATE 'NIL)))
          'NIL))))
      (CONS 'F-PUT-GLOBAL
            (CONS (CONS 'QUOTE
                        (CONS (CAR (CAR BINDINGS)) 'NIL))
                  (CONS VAL-FORM (CONS 'STATE 'NIL))))))
    (CONS 'CHECK-VARS-NOT-FREE
          (CONS (CONS 'STATE-GLOBAL-LET*-CLEANUP-LST
                      'NIL)
                (CONS (CAR (CDR (CAR BINDINGS))) 'NIL)))
    BINDINGS)
   (STATE-GLOBAL-LET*-PUT-GLOBALS (CDR BINDINGS)))))

(DEFUN
 STATE-GLOBAL-LET*-CLEANUP
 (BINDINGS INDEX)
 ((LAMBDA
   (CDR-EXPR INDEX BINDINGS)
   (IF
    (ENDP BINDINGS)
    'NIL
    (CONS
     (IF
      (CDR (CDR (CAR BINDINGS)))
      (CONS (CAR (CDR (CDR (CAR BINDINGS))))
            (CONS (CONS 'CAR
                        (CONS (CONS 'NTH
                                    (CONS INDEX (CONS CDR-EXPR 'NIL)))
                              'NIL))
                  (CONS 'STATE 'NIL)))
      (IF
       (ALWAYS-BOUNDP-GLOBAL (CAR (CAR BINDINGS)))
       (CONS 'F-PUT-GLOBAL
             (CONS (CONS 'QUOTE
                         (CONS (CAR (CAR BINDINGS)) 'NIL))
                   (CONS (CONS 'CAR
                               (CONS (CONS 'NTH
                                           (CONS INDEX (CONS CDR-EXPR 'NIL)))
                                     'NIL))
                         (CONS 'STATE 'NIL))))
       (CONS
        'IF
        (CONS
         (CONS 'NTH
               (CONS INDEX (CONS CDR-EXPR 'NIL)))
         (CONS
          (CONS
             'F-PUT-GLOBAL
             (CONS (CONS 'QUOTE
                         (CONS (CAR (CAR BINDINGS)) 'NIL))
                   (CONS (CONS 'CAR
                               (CONS (CONS 'NTH
                                           (CONS INDEX (CONS CDR-EXPR 'NIL)))
                                     'NIL))
                         (CONS 'STATE 'NIL))))
          (CONS (CONS 'MAKUNBOUND-GLOBAL
                      (CONS (CONS 'QUOTE
                                  (CONS (CAR (CAR BINDINGS)) 'NIL))
                            (CONS 'STATE 'NIL)))
                'NIL))))))
     (STATE-GLOBAL-LET*-CLEANUP (CDR BINDINGS)
                                (BINARY-+ '1 INDEX)))))
  'STATE-GLOBAL-LET*-CLEANUP-LST
  INDEX BINDINGS))

(DEFUN INTEGER-RANGE-P (LOWER UPPER X)
       (IF (INTEGERP X)
           (IF (NOT (< X LOWER)) (< X UPPER) 'NIL)
           'NIL))

(DEFUN SIGNED-BYTE-P (BITS X)
       (IF (INTEGERP BITS)
           (IF (< '0 BITS)
               (INTEGER-RANGE-P (UNARY-- (EXPT '2 (BINARY-+ '-1 BITS)))
                                (EXPT '2 (BINARY-+ '-1 BITS))
                                X)
               'NIL)
           'NIL))

(DEFUN UNSIGNED-BYTE-P (BITS X)
       (IF (INTEGERP BITS)
           (IF (NOT (< BITS '0))
               (INTEGER-RANGE-P '0 (EXPT '2 BITS) X)
               'NIL)
           'NIL))

(DEFTHM INTEGER-RANGE-P-FORWARD
        (IMPLIES (IF (INTEGER-RANGE-P LOWER (BINARY-+ '1 UPPER-1)
                                      X)
                     (INTEGERP UPPER-1)
                     'NIL)
                 (IF (INTEGERP X)
                     (IF (NOT (< X LOWER))
                         (NOT (< UPPER-1 X))
                         'NIL)
                     'NIL)))

(DEFTHM SIGNED-BYTE-P-FORWARD-TO-INTEGERP
        (IMPLIES (SIGNED-BYTE-P N X)
                 (INTEGERP X)))

(DEFTHM UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP
        (IMPLIES (UNSIGNED-BYTE-P N X)
                 (IF (INTEGERP X) (NOT (< X '0)) 'NIL)))

(DEFUN ZPF (X) (IF (INTEGERP X) (NOT (< '0 X)) 'T))

(DEFTHM STRING<-L-ASYMMETRIC
        (IMPLIES (IF (EQLABLE-LISTP X1)
                     (IF (EQLABLE-LISTP X2)
                         (IF (INTEGERP I)
                             (STRING<-L X1 X2 I)
                             'NIL)
                         'NIL)
                     'NIL)
                 (NOT (STRING<-L X2 X1 I))))

(DEFTHM SYMBOL-<-ASYMMETRIC
        (IMPLIES (IF (SYMBOLP SYM1)
                     (IF (SYMBOLP SYM2)
                         (SYMBOL-< SYM1 SYM2)
                         'NIL)
                     'NIL)
                 (NOT (SYMBOL-< SYM2 SYM1))))

(DEFTHM STRING<-L-TRANSITIVE
        (IMPLIES (IF (STRING<-L X Y I)
                     (IF (STRING<-L Y Z J)
                         (IF (INTEGERP I)
                             (IF (INTEGERP J)
                                 (IF (INTEGERP K)
                                     (IF (CHARACTER-LISTP X)
                                         (IF (CHARACTER-LISTP Y)
                                             (CHARACTER-LISTP Z)
                                             'NIL)
                                         'NIL)
                                     'NIL)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 (STRING<-L X Z K)))

(DEFTHM SYMBOL-<-TRANSITIVE
        (IMPLIES (IF (SYMBOL-< X Y)
                     (IF (SYMBOL-< Y Z)
                         (IF (SYMBOLP X)
                             (IF (SYMBOLP Y) (SYMBOLP Z) 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 (SYMBOL-< X Z)))

(DEFTHM STRING<-L-TRICHOTOMY
        (IMPLIES (IF (NOT (STRING<-L X Y I))
                     (IF (INTEGERP I)
                         (IF (INTEGERP J)
                             (IF (CHARACTER-LISTP X)
                                 (CHARACTER-LISTP Y)
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 (IFF (STRING<-L Y X J)
                      (NOT (EQUAL X Y)))))

(DEFTHM SYMBOL-<-TRICHOTOMY
        (IMPLIES (IF (SYMBOLP X)
                     (IF (SYMBOLP Y)
                         (NOT (SYMBOL-< X Y))
                         'NIL)
                     'NIL)
                 (IFF (SYMBOL-< Y X) (NOT (EQUAL X Y)))))

(DEFTHM ORDERED-SYMBOL-ALISTP-REMOVE-FIRST-PAIR
        (IMPLIES (IF (ORDERED-SYMBOL-ALISTP L)
                     (IF (SYMBOLP KEY) (ASSOC-EQ KEY L) 'NIL)
                     'NIL)
                 (ORDERED-SYMBOL-ALISTP (REMOVE-FIRST-PAIR KEY L))))

(DEFTHM SYMBOL-<-IRREFLEXIVE (IMPLIES (SYMBOLP X) (NOT (SYMBOL-< X X))))

(DEFTHM ORDERED-SYMBOL-ALISTP-ADD-PAIR
        (IMPLIES (IF (ORDERED-SYMBOL-ALISTP GS)
                     (SYMBOLP W5)
                     'NIL)
                 (ORDERED-SYMBOL-ALISTP (ADD-PAIR W5 W6 GS))))

(DEFTHM ORDERED-SYMBOL-ALISTP-GETPROPS
        (IMPLIES (IF (WORLDP W)
                     (IF (SYMBOLP WORLD-NAME)
                         (SYMBOLP KEY)
                         'NIL)
                     'NIL)
                 (ORDERED-SYMBOL-ALISTP (GETPROPS KEY WORLD-NAME W))))

(DEFUN INTEGER-LENGTH (I)
       (IF (ZIP I)
           '0
           (IF (= I '-1)
               '0
               (BINARY-+ '1
                         (INTEGER-LENGTH (FLOOR I '2))))))

(DEFUN
  BINARY-LOGAND (I J)
  (IF (ZIP I)
      '0
      (IF (ZIP J)
          '0
          (IF (EQL I '-1)
              J
              (IF (EQL J '-1)
                  I
                  ((LAMBDA (X J I)
                           (BINARY-+ X
                                     (IF (EVENP I) '0 (IF (EVENP J) '0 '1))))
                   (BINARY-* '2
                             (BINARY-LOGAND (FLOOR I '2)
                                            (FLOOR J '2)))
                   J I))))))

(DEFUN LOGNAND (I J) (LOGNOT (BINARY-LOGAND I J)))

(DEFUN BINARY-LOGIOR (I J) (LOGNOT (BINARY-LOGAND (LOGNOT I) (LOGNOT J))))

(DEFUN LOGORC1 (I J) (BINARY-LOGIOR (LOGNOT I) J))

(DEFUN LOGORC2 (I J) (BINARY-LOGIOR I (LOGNOT J)))

(DEFUN LOGANDC1 (I J) (BINARY-LOGAND (LOGNOT I) J))

(DEFUN LOGANDC2 (I J) (BINARY-LOGAND I (LOGNOT J)))

(DEFUN BINARY-LOGEQV (I J) (BINARY-LOGAND (LOGORC1 I J) (LOGORC1 J I)))

(DEFUN BINARY-LOGXOR (I J) (LOGNOT (BINARY-LOGEQV I J)))

(DEFUN LOGNOR (I J) (LOGNOT (BINARY-LOGIOR I J)))

(DEFUN LOGTEST (X Y) (NOT (ZEROP (BINARY-LOGAND X Y))))

(DEFUN
 BOOLE$ (OP I1 I2)
 (IF
  (EQL OP '0)
  I1
  (IF
   (EQL OP '1)
   I2
   (IF
    (EQL OP '2)
    (BINARY-LOGAND I1 I2)
    (IF (EQL OP '3)
        (LOGANDC1 I1 I2)
        (IF (EQL OP '4)
            (LOGANDC2 I1 I2)
            (IF (EQL OP '5)
                (LOGNOT I1)
                (IF (EQL OP '6)
                    (LOGNOT I2)
                    (IF (EQL OP '7)
                        '0
                        (IF (EQL OP '8)
                            (BINARY-LOGEQV I1 I2)
                            (IF (EQL OP '9)
                                (BINARY-LOGIOR I1 I2)
                                (IF (EQL OP '10)
                                    (LOGNAND I1 I2)
                                    (IF (EQL OP '11)
                                        (LOGNOR I1 I2)
                                        (IF (EQL OP '12)
                                            (LOGORC1 I1 I2)
                                            (IF (EQL OP '13)
                                                (LOGORC2 I1 I2)
                                                (IF (EQL OP '14)
                                                    '1
                                                    (IF (EQL OP '15)
                                                        (BINARY-LOGXOR I1 I2)
                                                        '0)))))))))))))))))

(DEFUN
     SET-FORMS-FROM-BINDINGS (BINDINGS)
     (IF (ENDP BINDINGS)
         'NIL
         (CONS (CONS (INTERN-IN-PACKAGE-OF-SYMBOL
                          (STRING-APPEND '"SET-"
                                         (SYMBOL-NAME (CAR (CAR BINDINGS))))
                          (PKG-WITNESS '"ACL2"))
                     (CONS (CAR (CDR (CAR BINDINGS)))
                           (CONS 'STATE 'NIL)))
               (SET-FORMS-FROM-BINDINGS (CDR BINDINGS)))))

(DEFUN ALIST-DIFFERENCE-EQ (ALIST1 ALIST2)
       (IF (ENDP ALIST1)
           'NIL
           (IF (ASSOC-EQ (CAR (CAR ALIST1)) ALIST2)
               (ALIST-DIFFERENCE-EQ (CDR ALIST1)
                                    ALIST2)
               (CONS (CAR ALIST1)
                     (ALIST-DIFFERENCE-EQ (CDR ALIST1)
                                          ALIST2)))))

(DEFUN
 DIGIT-TO-CHAR (N)
 (IF
  (EQL N '1)
  '#\1
  (IF
     (EQL N '2)
     '#\2
     (IF (EQL N '3)
         '#\3
         (IF (EQL N '4)
             '#\4
             (IF (EQL N '5)
                 '#\5
                 (IF (EQL N '6)
                     '#\6
                     (IF (EQL N '7)
                         '#\7
                         (IF (EQL N '8)
                             '#\8
                             (IF (EQL N '9)
                                 '#\9
                                 (IF (EQL N '10)
                                     '#\A
                                     (IF (EQL N '11)
                                         '#\B
                                         (IF (EQL N '12)
                                             '#\C
                                             (IF (EQL N '13)
                                                 '#\D
                                                 (IF (EQL N '14)
                                                     '#\E
                                                     (IF (EQL N '15)
                                                         '#\F
                                                         '#\0))))))))))))))))

(DEFUN PRINT-BASE-P (PRINT-BASE) (MEMBER PRINT-BASE '(2 8 10 16)))

(DEFUN
    EXPLODE-NONNEGATIVE-INTEGER
    (N PRINT-BASE ANS)
    (IF (IF (ZP N)
            (ZP N)
            (NOT (PRINT-BASE-P PRINT-BASE)))
        (IF (NULL ANS) '(#\0) ANS)
        (EXPLODE-NONNEGATIVE-INTEGER (FLOOR N PRINT-BASE)
                                     PRINT-BASE
                                     (CONS (DIGIT-TO-CHAR (MOD N PRINT-BASE))
                                           ANS))))

(DEFUN
 EXPLODE-ATOM (X PRINT-BASE)
 (IF
  (RATIONALP X)
  (IF (INTEGERP X)
      ((LAMBDA (DIGITS PRINT-BASE)
               (IF (EQL '10
                        ((LAMBDA (VAR)
                                 (IF (INTEGERP VAR)
                                     VAR (THE-ERROR 'INTEGER VAR)))
                         PRINT-BASE))
                   DIGITS
                   (CONS '#\#
                         (CONS (IF (EQL PRINT-BASE '2)
                                   '#\b
                                   (IF (EQL PRINT-BASE '8)
                                       '#\o
                                       (IF (EQL PRINT-BASE '16)
                                           '#\x
                                           (ILLEGAL 'EXPLODE-ATOM
                                                    '"Unexpected base, ~x0"
                                                    PRINT-BASE))))
                               DIGITS))))
       (IF (< X '0)
           (CONS '#\-
                 (EXPLODE-NONNEGATIVE-INTEGER (UNARY-- X)
                                              PRINT-BASE 'NIL))
           (EXPLODE-NONNEGATIVE-INTEGER X PRINT-BASE 'NIL))
       PRINT-BASE)
      (BINARY-APPEND (EXPLODE-ATOM (NUMERATOR X) PRINT-BASE)
                     (CONS '#\/
                           (EXPLODE-NONNEGATIVE-INTEGER (DENOMINATOR X)
                                                        PRINT-BASE 'NIL))))
  (IF
   (COMPLEX-RATIONALP X)
   (CONS
    '#\#
    (CONS
       '#\C
       (CONS '#\(
             (BINARY-APPEND
                  (EXPLODE-ATOM (REALPART X) PRINT-BASE)
                  (CONS '#\Space
                        (BINARY-APPEND (EXPLODE-ATOM (IMAGPART X) PRINT-BASE)
                                       '(#\))))))))
   (IF (CHARACTERP X)
       (CONS X 'NIL)
       (IF (STRINGP X)
           (COERCE X 'LIST)
           (COERCE (SYMBOL-NAME X) 'LIST))))))

(DEFTHM TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP-ASSOC-EQ
        (IMPLIES (TRUE-LIST-LISTP L)
                 (TRUE-LISTP (ASSOC-EQ KEY L))))

(DEFTHM TRUE-LISTP-CADR-ASSOC-EQ-FOR-OPEN-CHANNELS-P
        (IMPLIES (OPEN-CHANNELS-P ALIST)
                 (TRUE-LISTP (CAR (CDR (ASSOC-EQ KEY ALIST))))))

(DEFUN OPEN-INPUT-CHANNEL-P1
       (CHANNEL TYP STATE-STATE)
       ((LAMBDA (PAIR TYP)
                (IF PAIR
                    (EQ (CAR (CDR (CAR (CDR PAIR)))) TYP)
                    'NIL))
        (ASSOC-EQ CHANNEL
                  (OPEN-INPUT-CHANNELS STATE-STATE))
        TYP))

(DEFUN OPEN-OUTPUT-CHANNEL-P1
       (CHANNEL TYP STATE-STATE)
       ((LAMBDA (PAIR TYP)
                (IF PAIR
                    (EQ (CAR (CDR (CAR (CDR PAIR)))) TYP)
                    'NIL))
        (ASSOC-EQ CHANNEL
                  (OPEN-OUTPUT-CHANNELS STATE-STATE))
        TYP))

(DEFUN OPEN-INPUT-CHANNEL-P
       (CHANNEL TYP STATE-STATE)
       (OPEN-INPUT-CHANNEL-P1 CHANNEL TYP STATE-STATE))

(DEFUN OPEN-OUTPUT-CHANNEL-P
       (CHANNEL TYP STATE-STATE)
       (OPEN-OUTPUT-CHANNEL-P1 CHANNEL TYP STATE-STATE))

(DEFUN OPEN-OUTPUT-CHANNEL-ANY-P1
       (CHANNEL STATE-STATE)
       (IF (OPEN-OUTPUT-CHANNEL-P1 CHANNEL ':CHARACTER
                                   STATE-STATE)
           (OPEN-OUTPUT-CHANNEL-P1 CHANNEL ':CHARACTER
                                   STATE-STATE)
           (IF (OPEN-OUTPUT-CHANNEL-P1 CHANNEL ':BYTE
                                       STATE-STATE)
               (OPEN-OUTPUT-CHANNEL-P1 CHANNEL ':BYTE
                                       STATE-STATE)
               (OPEN-OUTPUT-CHANNEL-P1 CHANNEL ':OBJECT
                                       STATE-STATE))))

(DEFUN OPEN-OUTPUT-CHANNEL-ANY-P
       (CHANNEL STATE-STATE)
       (OPEN-OUTPUT-CHANNEL-ANY-P1 CHANNEL STATE-STATE))

(DEFUN OPEN-INPUT-CHANNEL-ANY-P1
       (CHANNEL STATE-STATE)
       (IF (OPEN-INPUT-CHANNEL-P1 CHANNEL ':CHARACTER
                                  STATE-STATE)
           (OPEN-INPUT-CHANNEL-P1 CHANNEL ':CHARACTER
                                  STATE-STATE)
           (IF (OPEN-INPUT-CHANNEL-P1 CHANNEL ':BYTE
                                      STATE-STATE)
               (OPEN-INPUT-CHANNEL-P1 CHANNEL ':BYTE
                                      STATE-STATE)
               (OPEN-INPUT-CHANNEL-P1 CHANNEL ':OBJECT
                                      STATE-STATE))))

(DEFUN OPEN-INPUT-CHANNEL-ANY-P
       (CHANNEL STATE-STATE)
       (OPEN-INPUT-CHANNEL-ANY-P1 CHANNEL STATE-STATE))

(DEFUN
 SET-PRINT-CASE (CASE STATE)
 (PROG2$
  (IF
   (EQ CASE ':UPCASE)
   (EQ CASE ':UPCASE)
   (IF
    (EQ CASE ':DOWNCASE)
    (EQ CASE ':DOWNCASE)
    (ILLEGAL
     'SET-PRINT-CASE
     '"The value ~x0 is illegal as an ACL2 print-base, which ~
                        must be :UPCASE or :DOWNCASE."
     (CONS (CONS '#\0 CASE) 'NIL))))
  (PUT-GLOBAL 'PRINT-CASE CASE STATE)))

(DEFUN
 CHECK-PRINT-BASE (PRINT-BASE CTX)
 (IF
  (PRINT-BASE-P PRINT-BASE)
  'NIL
  (HARD-ERROR
   CTX
   '"The value ~x0 is illegal as a print-base, which must be 2, ~
                 8, 10, or 16"
   (CONS (CONS '#\0 PRINT-BASE) 'NIL))))

(DEFUN SET-PRINT-BASE (BASE STATE)
       (PROG2$ (CHECK-PRINT-BASE BASE 'SET-PRINT-BASE)
               (PUT-GLOBAL 'PRINT-BASE BASE STATE)))

(DEFUN SET-PRINT-CIRCLE (X STATE) (PUT-GLOBAL 'PRINT-CIRCLE X STATE))

(DEFUN SET-PRINT-ESCAPE (X STATE) (PUT-GLOBAL 'PRINT-ESCAPE X STATE))

(DEFUN SET-PRINT-PRETTY (X STATE) (PUT-GLOBAL 'PRINT-PRETTY X STATE))

(DEFUN SET-PRINT-RADIX (X STATE) (PUT-GLOBAL 'PRINT-RADIX X STATE))

(DEFUN SET-PRINT-READABLY (X STATE) (PUT-GLOBAL 'PRINT-READABLY X STATE))

(DEFUN
 CHECK-NULL-OR-NATP (N FN)
 (IF
  (NULL N)
  (NULL N)
  (IF
   (NATP N)
   (NATP N)
   (HARD-ERROR
    FN
    '"The argument of ~x0 must be ~x1 or a positive integer, but ~
                   ~x2 is neither."
    (CONS (CONS '#\0 FN)
          (CONS (CONS '#\1 'NIL)
                (CONS (CONS '#\2 N) 'NIL)))))))

(DEFUN SET-PRINT-LENGTH (N STATE)
       (PROG2$ (CHECK-NULL-OR-NATP N 'SET-PRINT-LENGTH)
               (PUT-GLOBAL 'PRINT-LENGTH N STATE)))

(DEFUN SET-PRINT-LEVEL (N STATE)
       (PROG2$ (CHECK-NULL-OR-NATP N 'SET-PRINT-LEVEL)
               (PUT-GLOBAL 'PRINT-LEVEL N STATE)))

(DEFUN SET-PRINT-LINES (N STATE)
       (PROG2$ (CHECK-NULL-OR-NATP N 'SET-PRINT-LINES)
               (PUT-GLOBAL 'PRINT-LINES N STATE)))

(DEFUN SET-PRINT-RIGHT-MARGIN (N STATE)
       (PROG2$ (CHECK-NULL-OR-NATP N 'SET-PRINT-RIGHT-MARGIN)
               (PUT-GLOBAL 'PRINT-RIGHT-MARGIN
                           N STATE)))

(DEFUN
 PRINC$ (X CHANNEL STATE-STATE)
 ((LAMBDA
   (ENTRY STATE-STATE X CHANNEL)
   (UPDATE-OPEN-OUTPUT-CHANNELS
    (ADD-PAIR
     CHANNEL
     (CONS
         (CAR ENTRY)
         (REVAPPEND
              (IF (IF (SYMBOLP X)
                      (EQ (CDR (ASSOC-EQ 'PRINT-CASE
                                         (GLOBAL-TABLE STATE-STATE)))
                          ':DOWNCASE)
                      'NIL)
                  (COERCE (STRING-DOWNCASE (SYMBOL-NAME X))
                          'LIST)
                  (EXPLODE-ATOM X
                                (CDR (ASSOC-EQ 'PRINT-BASE
                                               (GLOBAL-TABLE STATE-STATE)))))
              (CDR ENTRY)))
     (OPEN-OUTPUT-CHANNELS STATE-STATE))
    STATE-STATE))
  (CDR (ASSOC-EQ CHANNEL
                 (OPEN-OUTPUT-CHANNELS STATE-STATE)))
  STATE-STATE X CHANNEL))

(DEFUN WRITE-BYTE$ (X CHANNEL STATE-STATE)
       ((LAMBDA (ENTRY STATE-STATE X CHANNEL)
                (UPDATE-OPEN-OUTPUT-CHANNELS
                     (ADD-PAIR CHANNEL
                               (CONS (CAR ENTRY) (CONS X (CDR ENTRY)))
                               (OPEN-OUTPUT-CHANNELS STATE-STATE))
                     STATE-STATE))
        (CDR (ASSOC-EQ CHANNEL
                       (OPEN-OUTPUT-CHANNELS STATE-STATE)))
        STATE-STATE X CHANNEL))

(DEFUN PRINT-OBJECT$ (X CHANNEL STATE-STATE)
       ((LAMBDA (ENTRY STATE-STATE X CHANNEL)
                (UPDATE-OPEN-OUTPUT-CHANNELS
                     (ADD-PAIR CHANNEL
                               (CONS (CAR ENTRY) (CONS X (CDR ENTRY)))
                               (OPEN-OUTPUT-CHANNELS STATE-STATE))
                     STATE-STATE))
        (CDR (ASSOC-EQ CHANNEL
                       (OPEN-OUTPUT-CHANNELS STATE-STATE)))
        STATE-STATE X CHANNEL))

(DEFUN MAKE-INPUT-CHANNEL (FILE-NAME CLOCK)
       (INTERN-IN-PACKAGE-OF-SYMBOL
            (COERCE (BINARY-APPEND (COERCE FILE-NAME 'LIST)
                                   (CONS '#\- (EXPLODE-ATOM CLOCK '10)))
                    'STRING)
            'ACL2-INPUT-CHANNEL::A-RANDOM-SYMBOL-FOR-INTERN))

(DEFUN MAKE-OUTPUT-CHANNEL (FILE-NAME CLOCK)
       (INTERN-IN-PACKAGE-OF-SYMBOL
            (COERCE (BINARY-APPEND (COERCE FILE-NAME 'LIST)
                                   (CONS '#\- (EXPLODE-ATOM CLOCK '10)))
                    'STRING)
            'ACL2-OUTPUT-CHANNEL::A-RANDOM-SYMBOL-FOR-INTERN))

(DEFUN
 OPEN-INPUT-CHANNEL
 (FILE-NAME TYP STATE-STATE)
 ((LAMBDA
   (STATE-STATE TYP FILE-NAME)
   ((LAMBDA
     (PAIR TYP STATE-STATE FILE-NAME)
     (IF
      PAIR
      ((LAMBDA
        (CHANNEL PAIR STATE-STATE FILE-NAME TYP)
        (CONS
         CHANNEL
         (CONS
          (UPDATE-OPEN-INPUT-CHANNELS
           (ADD-PAIR
              CHANNEL
              (CONS (CONS ':HEADER
                          (CONS TYP
                                (CONS FILE-NAME
                                      (CONS (FILE-CLOCK STATE-STATE) 'NIL))))
                    (CDR PAIR))
              (OPEN-INPUT-CHANNELS STATE-STATE))
           STATE-STATE)
          'NIL)))
       (MAKE-INPUT-CHANNEL FILE-NAME (FILE-CLOCK STATE-STATE))
       PAIR STATE-STATE FILE-NAME TYP)
      (CONS 'NIL (CONS STATE-STATE 'NIL))))
    (ASSOC-EQUAL (CONS FILE-NAME
                       (CONS TYP
                             (CONS (FILE-CLOCK STATE-STATE) 'NIL)))
                 (READABLE-FILES STATE-STATE))
    TYP STATE-STATE FILE-NAME))
  (UPDATE-FILE-CLOCK (BINARY-+ '1 (FILE-CLOCK STATE-STATE))
                     STATE-STATE)
  TYP FILE-NAME))

(DEFTHM NTH-UPDATE-NTH
        (EQUAL (NTH M (UPDATE-NTH N VAL L))
               (IF (EQUAL (NFIX M) (NFIX N))
                   VAL (NTH M L))))

(DEFTHM TRUE-LISTP-UPDATE-NTH
        (IMPLIES (TRUE-LISTP L)
                 (TRUE-LISTP (UPDATE-NTH KEY VAL L))))

(DEFTHM NTH-UPDATE-NTH-ARRAY
        (EQUAL (NTH M (UPDATE-NTH-ARRAY N I VAL L))
               (IF (EQUAL (NFIX M) (NFIX N))
                   (UPDATE-NTH I VAL (NTH M L))
                   (NTH M L))))

(DEFUN
 CLOSE-INPUT-CHANNEL
 (CHANNEL STATE-STATE)
 ((LAMBDA
   (STATE-STATE CHANNEL)
   ((LAMBDA
        (HEADER-ENTRIES CHANNEL STATE-STATE)
        ((LAMBDA (STATE-STATE CHANNEL)
                 ((LAMBDA (STATE-STATE) STATE-STATE)
                  (UPDATE-OPEN-INPUT-CHANNELS
                       (DELETE-PAIR CHANNEL
                                    (OPEN-INPUT-CHANNELS STATE-STATE))
                       STATE-STATE)))
         (UPDATE-READ-FILES
              (CONS (CONS (CAR (CDR HEADER-ENTRIES))
                          (CONS (CAR HEADER-ENTRIES)
                                (CONS (CAR (CDR (CDR HEADER-ENTRIES)))
                                      (CONS (FILE-CLOCK STATE-STATE) 'NIL))))
                    (READ-FILES STATE-STATE))
              STATE-STATE)
         CHANNEL))
    (CDR (CAR (CDR (ASSOC-EQ CHANNEL
                             (OPEN-INPUT-CHANNELS STATE-STATE)))))
    CHANNEL STATE-STATE))
  (UPDATE-FILE-CLOCK (BINARY-+ '1 (FILE-CLOCK STATE-STATE))
                     STATE-STATE)
  CHANNEL))

(DEFUN
 OPEN-OUTPUT-CHANNEL
 (FILE-NAME TYP STATE-STATE)
 ((LAMBDA
   (STATE-STATE TYP FILE-NAME)
   (IF
    (MEMBER-EQUAL (CONS FILE-NAME
                        (CONS TYP
                              (CONS (FILE-CLOCK STATE-STATE) 'NIL)))
                  (WRITEABLE-FILES STATE-STATE))
    ((LAMBDA
      (CHANNEL STATE-STATE FILE-NAME TYP)
      (CONS
       CHANNEL
       (CONS
        (UPDATE-OPEN-OUTPUT-CHANNELS
         (ADD-PAIR
              CHANNEL
              (CONS (CONS ':HEADER
                          (CONS TYP
                                (CONS FILE-NAME
                                      (CONS (FILE-CLOCK STATE-STATE) 'NIL))))
                    'NIL)
              (OPEN-OUTPUT-CHANNELS STATE-STATE))
         STATE-STATE)
        'NIL)))
     (MAKE-OUTPUT-CHANNEL FILE-NAME (FILE-CLOCK STATE-STATE))
     STATE-STATE FILE-NAME TYP)
    (CONS 'NIL (CONS STATE-STATE 'NIL))))
  (UPDATE-FILE-CLOCK (BINARY-+ '1 (FILE-CLOCK STATE-STATE))
                     STATE-STATE)
  TYP FILE-NAME))

(DEFUN
 OPEN-OUTPUT-CHANNEL!
 (FILE-NAME TYP STATE)
 ((LAMBDA (MV)
          ((LAMBDA (ERP CHAN STATE)
                   (CONS CHAN (CONS STATE 'NIL)))
           (HIDE (MV-NTH '0 MV))
           (MV-NTH '1 MV)
           (MV-NTH '2 MV)))
  ((LAMBDA
    (STATE-GLOBAL-LET*-CLEANUP-LST FILE-NAME TYP STATE)
    ((LAMBDA
      (MV STATE-GLOBAL-LET*-CLEANUP-LST)
      ((LAMBDA (ACL2-UNWIND-PROTECT-ERP ACL2-UNWIND-PROTECT-VAL
                                        STATE STATE-GLOBAL-LET*-CLEANUP-LST)
               (IF ACL2-UNWIND-PROTECT-ERP
                   ((LAMBDA (STATE ACL2-UNWIND-PROTECT-VAL
                                   ACL2-UNWIND-PROTECT-ERP)
                            (CONS ACL2-UNWIND-PROTECT-ERP
                                  (CONS ACL2-UNWIND-PROTECT-VAL
                                        (CONS STATE 'NIL))))
                    ((LAMBDA (STATE) STATE)
                     (PUT-GLOBAL 'WRITES-OKP
                                 (CAR (NTH '0 STATE-GLOBAL-LET*-CLEANUP-LST))
                                 STATE))
                    ACL2-UNWIND-PROTECT-VAL
                    ACL2-UNWIND-PROTECT-ERP)
                   ((LAMBDA (STATE ACL2-UNWIND-PROTECT-VAL
                                   ACL2-UNWIND-PROTECT-ERP)
                            (CONS ACL2-UNWIND-PROTECT-ERP
                                  (CONS ACL2-UNWIND-PROTECT-VAL
                                        (CONS STATE 'NIL))))
                    ((LAMBDA (STATE) STATE)
                     (PUT-GLOBAL 'WRITES-OKP
                                 (CAR (NTH '0 STATE-GLOBAL-LET*-CLEANUP-LST))
                                 STATE))
                    ACL2-UNWIND-PROTECT-VAL
                    ACL2-UNWIND-PROTECT-ERP)))
       (MV-NTH '0 MV)
       (MV-NTH '1 MV)
       (MV-NTH '2 MV)
       STATE-GLOBAL-LET*-CLEANUP-LST))
     ((LAMBDA (STATE TYP FILE-NAME)
              ((LAMBDA (MV)
                       ((LAMBDA (CHAN STATE)
                                (CONS 'NIL
                                      (CONS CHAN (CONS STATE 'NIL))))
                        (MV-NTH '0 MV)
                        (MV-NTH '1 MV)))
               (OPEN-OUTPUT-CHANNEL FILE-NAME TYP STATE)))
      (PUT-GLOBAL 'WRITES-OKP 'T STATE)
      TYP FILE-NAME)
     STATE-GLOBAL-LET*-CLEANUP-LST))
   (CONS (CONS (GET-GLOBAL 'WRITES-OKP STATE)
               'NIL)
         'NIL)
   FILE-NAME TYP STATE)))

(DEFUN
 CLOSE-OUTPUT-CHANNEL
 (CHANNEL STATE-STATE)
 ((LAMBDA
   (STATE-STATE CHANNEL)
   ((LAMBDA
     (PAIR STATE-STATE CHANNEL)
     ((LAMBDA
       (HEADER-ENTRIES CHANNEL PAIR STATE-STATE)
       ((LAMBDA (STATE-STATE CHANNEL)
                ((LAMBDA (STATE-STATE) STATE-STATE)
                 (UPDATE-OPEN-OUTPUT-CHANNELS
                      (DELETE-PAIR CHANNEL
                                   (OPEN-OUTPUT-CHANNELS STATE-STATE))
                      STATE-STATE)))
        (UPDATE-WRITTEN-FILES
         (CONS
              (CONS (CONS (CAR (CDR HEADER-ENTRIES))
                          (CONS (CAR HEADER-ENTRIES)
                                (CONS (CAR (CDR (CDR HEADER-ENTRIES)))
                                      (CONS (FILE-CLOCK STATE-STATE) 'NIL))))
                    (CDR (CDR PAIR)))
              (WRITTEN-FILES STATE-STATE))
         STATE-STATE)
        CHANNEL))
      (CDR (CAR (CDR PAIR)))
      CHANNEL PAIR STATE-STATE))
    (ASSOC-EQ CHANNEL
              (OPEN-OUTPUT-CHANNELS STATE-STATE))
    STATE-STATE CHANNEL))
  (UPDATE-FILE-CLOCK (BINARY-+ '1 (FILE-CLOCK STATE-STATE))
                     STATE-STATE)
  CHANNEL))

(DEFUN
     READ-CHAR$ (CHANNEL STATE-STATE)
     ((LAMBDA (ENTRY STATE-STATE CHANNEL)
              (CONS (CAR (CDR ENTRY))
                    (CONS (UPDATE-OPEN-INPUT-CHANNELS
                               (ADD-PAIR CHANNEL
                                         (CONS (CAR ENTRY) (CDR (CDR ENTRY)))
                                         (OPEN-INPUT-CHANNELS STATE-STATE))
                               STATE-STATE)
                          'NIL)))
      (CDR (ASSOC-EQ CHANNEL
                     (OPEN-INPUT-CHANNELS STATE-STATE)))
      STATE-STATE CHANNEL))

(DEFUN PEEK-CHAR$ (CHANNEL STATE-STATE)
       ((LAMBDA (ENTRY) (CAR (CDR ENTRY)))
        (CDR (ASSOC-EQ CHANNEL
                       (OPEN-INPUT-CHANNELS STATE-STATE)))))

(DEFUN
     READ-BYTE$ (CHANNEL STATE-STATE)
     ((LAMBDA (ENTRY STATE-STATE CHANNEL)
              (CONS (CAR (CDR ENTRY))
                    (CONS (UPDATE-OPEN-INPUT-CHANNELS
                               (ADD-PAIR CHANNEL
                                         (CONS (CAR ENTRY) (CDR (CDR ENTRY)))
                                         (OPEN-INPUT-CHANNELS STATE-STATE))
                               STATE-STATE)
                          'NIL)))
      (CDR (ASSOC-EQ CHANNEL
                     (OPEN-INPUT-CHANNELS STATE-STATE)))
      STATE-STATE CHANNEL))

(DEFUN
 READ-OBJECT (CHANNEL STATE-STATE)
 ((LAMBDA
    (ENTRY STATE-STATE CHANNEL)
    (IF (CDR ENTRY)
        (CONS 'NIL
              (CONS (CAR (CDR ENTRY))
                    (CONS (UPDATE-OPEN-INPUT-CHANNELS
                               (ADD-PAIR CHANNEL
                                         (CONS (CAR ENTRY) (CDR (CDR ENTRY)))
                                         (OPEN-INPUT-CHANNELS STATE-STATE))
                               STATE-STATE)
                          'NIL)))
        (CONS 'T
              (CONS 'NIL (CONS STATE-STATE 'NIL)))))
  (CDR (ASSOC-EQ CHANNEL
                 (OPEN-INPUT-CHANNELS STATE-STATE)))
  STATE-STATE CHANNEL))

(DEFUN SOME-SLASHABLE (L)
       (IF (ENDP L)
           'NIL
           (IF (MEMBER (CAR L)
                       '(#\Newline #\Page
                                   #\Space #\" #\# #\' #\( #\) #\, #\: #\;
                                   #\\ #\` #\a #\b #\c #\d #\e #\f #\g #\h
                                   #\i #\j #\k #\l #\m #\n #\o #\p #\q #\r
                                   #\s #\t #\u #\v #\w #\x #\y #\z #\|))
               'T
               (SOME-SLASHABLE (CDR L)))))

(DEFUN PRIN1-WITH-SLASHES1
       (L SLASH-CHAR CHANNEL STATE)
       (IF (ENDP L)
           STATE
           ((LAMBDA (STATE SLASH-CHAR CHANNEL L)
                    ((LAMBDA (STATE CHANNEL SLASH-CHAR L)
                             (PRIN1-WITH-SLASHES1 (CDR L)
                                                  SLASH-CHAR CHANNEL STATE))
                     (PRINC$ (CAR L) CHANNEL STATE)
                     CHANNEL SLASH-CHAR L))
            (IF (IF (EQUAL (CAR L) '#\\)
                    (EQUAL (CAR L) '#\\)
                    (EQUAL (CAR L) SLASH-CHAR))
                (PRINC$ '#\\ CHANNEL STATE)
                STATE)
            SLASH-CHAR CHANNEL L)))

(DEFUN PRIN1-WITH-SLASHES
       (S SLASH-CHAR CHANNEL STATE)
       (PRIN1-WITH-SLASHES1 (COERCE S 'LIST)
                            SLASH-CHAR CHANNEL STATE))

(DEFUN MAY-NEED-SLASHES1 (LST FLG POTNUM-CHARS)
       (IF (ENDP LST)
           'T
           (IF (MEMBER (CAR LST) POTNUM-CHARS)
               (MAY-NEED-SLASHES1 (CDR LST)
                                  'NIL
                                  POTNUM-CHARS)
               (IF (MEMBER (CAR LST)
                           '(#\A #\B #\C
                                 #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M
                                 #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W
                                 #\X #\Y #\Z #\a #\b #\c #\d #\e #\f #\g
                                 #\h #\i #\j #\k #\l #\m #\n #\o #\p #\q
                                 #\r #\s #\t #\u #\v #\w #\x #\y #\z))
                   (IF FLG 'NIL
                       (MAY-NEED-SLASHES1 (CDR LST)
                                          'T
                                          POTNUM-CHARS))
                   'NIL))))

(DEFUN
 MAY-NEED-SLASHES-FN (X PRINT-BASE)
 ((LAMBDA
   (L PRINT-BASE)
   ((LAMBDA
     (PRINT-BASE L)
     ((LAMBDA
       (NUMERIC-CHARS L PRINT-BASE)
       ((LAMBDA
         (SUSPICIOUSLY-FIRST-NUMERIC-CHARS NUMERIC-CHARS L)
         (IF
          (NULL L)
          (NULL L)
          (IF
           (IF
              (IF (MEMBER (CAR L) NUMERIC-CHARS)
                  (MEMBER (CAR L) NUMERIC-CHARS)
                  (IF (MEMBER (CAR L)
                              SUSPICIOUSLY-FIRST-NUMERIC-CHARS)
                      (INTERSECTP (CDR L) NUMERIC-CHARS)
                      'NIL))
              (IF (NOT (MEMBER (CAR (LAST L)) '(#\+ #\-)))
                  (MAY-NEED-SLASHES1 (CDR L)
                                     'NIL
                                     (CONS '#\/
                                           SUSPICIOUSLY-FIRST-NUMERIC-CHARS))
                  'NIL)
              'NIL)
           (IF
              (IF (MEMBER (CAR L) NUMERIC-CHARS)
                  (MEMBER (CAR L) NUMERIC-CHARS)
                  (IF (MEMBER (CAR L)
                              SUSPICIOUSLY-FIRST-NUMERIC-CHARS)
                      (INTERSECTP (CDR L) NUMERIC-CHARS)
                      'NIL))
              (IF (NOT (MEMBER (CAR (LAST L)) '(#\+ #\-)))
                  (MAY-NEED-SLASHES1 (CDR L)
                                     'NIL
                                     (CONS '#\/
                                           SUSPICIOUSLY-FIRST-NUMERIC-CHARS))
                  'NIL)
              'NIL)
           (SOME-SLASHABLE L))))
        (IF (EQL PRINT-BASE '16)
            '(#\0 #\1 #\2 #\3 #\4 #\5 #\6
                  #\7 #\8 #\9 #\A #\B #\C #\D #\E #\F #\a
                  #\b #\c #\d #\e #\f #\+ #\- #\. #\^ #\_)
            '(#\0 #\1 #\2 #\3 #\4 #\5
                  #\6 #\7 #\8 #\9 #\+ #\- #\. #\^ #\_))
        NUMERIC-CHARS L))
      (IF (EQL PRINT-BASE '16)
          '(#\0 #\1
                #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\A #\B
                #\C #\D #\E #\F #\a #\b #\c #\d #\e #\f)
          '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
      L PRINT-BASE))
    (IF (IF (EQL PRINT-BASE '16)
            (MEMBER '#\. L)
            'NIL)
        '10
        PRINT-BASE)
    L))
  (COERCE X 'LIST)
  PRINT-BASE))

(DEFUN NEEDS-SLASHES (X STATE)
       (IF (IF (GET-GLOBAL 'PRINT-ESCAPE STATE)
               (GET-GLOBAL 'PRINT-ESCAPE STATE)
               (GET-GLOBAL 'PRINT-READABLY STATE))
           (MAY-NEED-SLASHES-FN X (GET-GLOBAL 'PRINT-BASE STATE))
           'NIL))

(DEFUN T-STACK-LENGTH1 (STATE-STATE) (LENGTH (T-STACK STATE-STATE)))

(DEFUN T-STACK-LENGTH (STATE-STATE) (T-STACK-LENGTH1 STATE-STATE))

(DEFUN MAKE-LIST-AC (N VAL AC)
       (IF (ZP N)
           AC
           (MAKE-LIST-AC (BINARY-+ '-1 N)
                         VAL (CONS VAL AC))))

(DEFUN EXTEND-T-STACK (N VAL STATE-STATE)
       (UPDATE-T-STACK (BINARY-APPEND (T-STACK STATE-STATE)
                                      (MAKE-LIST-AC N VAL 'NIL))
                       STATE-STATE))

(DEFUN SUBSEQ-LIST (LST START END)
       (TAKE (BINARY-+ END (UNARY-- START))
             (NTHCDR START LST)))

(DEFUN SUBSEQ (SEQ START END)
       (IF (STRINGP SEQ)
           (COERCE (SUBSEQ-LIST (COERCE SEQ 'LIST)
                                START (IF END END (LENGTH SEQ)))
                   'STRING)
           (SUBSEQ-LIST SEQ START (IF END END (LENGTH SEQ)))))

(DEFUN
    SHRINK-T-STACK (N STATE-STATE)
    (UPDATE-T-STACK (FIRST-N-AC (MAX '0
                                     (BINARY-+ (LENGTH (T-STACK STATE-STATE))
                                               (UNARY-- N)))
                                (T-STACK STATE-STATE)
                                'NIL)
                    STATE-STATE))

(DEFUN AREF-T-STACK (I STATE-STATE) (NTH I (T-STACK STATE-STATE)))

(DEFUN ASET-T-STACK (I VAL STATE-STATE)
       (UPDATE-T-STACK (UPDATE-NTH I VAL (T-STACK STATE-STATE))
                       STATE-STATE))

(DEFUN 32-BIT-INTEGER-STACK-LENGTH1
       (STATE-STATE)
       (LENGTH (32-BIT-INTEGER-STACK STATE-STATE)))

(DEFUN 32-BIT-INTEGER-STACK-LENGTH
       (STATE-STATE)
       (32-BIT-INTEGER-STACK-LENGTH1 STATE-STATE))

(DEFUN EXTEND-32-BIT-INTEGER-STACK
       (N VAL STATE-STATE)
       (UPDATE-32-BIT-INTEGER-STACK
            (BINARY-APPEND (32-BIT-INTEGER-STACK STATE-STATE)
                           (MAKE-LIST-AC N VAL 'NIL))
            STATE-STATE))

(DEFUN
  SHRINK-32-BIT-INTEGER-STACK
  (N STATE-STATE)
  (UPDATE-32-BIT-INTEGER-STACK
       (FIRST-N-AC (MAX '0
                        (BINARY-+ (LENGTH (32-BIT-INTEGER-STACK STATE-STATE))
                                  (UNARY-- N)))
                   (32-BIT-INTEGER-STACK STATE-STATE)
                   'NIL)
       STATE-STATE))

(DEFUN AREF-32-BIT-INTEGER-STACK
       (I STATE-STATE)
       (NTH I (32-BIT-INTEGER-STACK STATE-STATE)))

(DEFUN ASET-32-BIT-INTEGER-STACK
       (I VAL STATE-STATE)
       (UPDATE-32-BIT-INTEGER-STACK
            (UPDATE-NTH I
                        VAL (32-BIT-INTEGER-STACK STATE-STATE))
            STATE-STATE))

(DEFUN BIG-CLOCK-NEGATIVE-P (STATE-STATE)
       (< (BIG-CLOCK-ENTRY STATE-STATE) '0))

(DEFUN DECREMENT-BIG-CLOCK (STATE-STATE)
       (UPDATE-BIG-CLOCK-ENTRY (BINARY-+ '-1
                                         (BIG-CLOCK-ENTRY STATE-STATE))
                               STATE-STATE))

(DEFUN LIST-ALL-PACKAGE-NAMES (STATE-STATE)
       (CONS (CAR (LIST-ALL-PACKAGE-NAMES-LST STATE-STATE))
             (CONS (UPDATE-LIST-ALL-PACKAGE-NAMES-LST
                        (CDR (LIST-ALL-PACKAGE-NAMES-LST STATE-STATE))
                        STATE-STATE)
                   'NIL)))

(DEFUN USER-STOBJ-ALIST (STATE-STATE) (USER-STOBJ-ALIST1 STATE-STATE))

(DEFUN UPDATE-USER-STOBJ-ALIST (X STATE-STATE)
       (UPDATE-USER-STOBJ-ALIST1 X STATE-STATE))

(DEFUN POWER-EVAL (L B)
       (IF (ENDP L)
           '0
           (BINARY-+ (CAR L)
                     (BINARY-* B (POWER-EVAL (CDR L) B)))))

(DEFUN READ-IDATE (STATE-STATE)
       (CONS (IF (NULL (IDATES STATE-STATE))
                 '0
                 (CAR (IDATES STATE-STATE)))
             (CONS (UPDATE-IDATES (CDR (IDATES STATE-STATE))
                                  STATE-STATE)
                   'NIL)))

(DEFUN READ-RUN-TIME (STATE-STATE)
       (CONS (IF (IF (NULL (ACL2-ORACLE STATE-STATE))
                     (NULL (ACL2-ORACLE STATE-STATE))
                     (NOT (RATIONALP (CAR (ACL2-ORACLE STATE-STATE)))))
                 '0
                 (CAR (ACL2-ORACLE STATE-STATE)))
             (CONS (UPDATE-ACL2-ORACLE (CDR (ACL2-ORACLE STATE-STATE))
                                       STATE-STATE)
                   'NIL)))

(DEFUN READ-ACL2-ORACLE (STATE-STATE)
       (CONS (NULL (ACL2-ORACLE STATE-STATE))
             (CONS (CAR (ACL2-ORACLE STATE-STATE))
                   (CONS (UPDATE-ACL2-ORACLE (CDR (ACL2-ORACLE STATE-STATE))
                                             STATE-STATE)
                         'NIL))))

(DEFUN GETENV$ (STR STATE) (READ-ACL2-ORACLE STATE))

(DEFUN SETENV$ (STR VAL) 'NIL)

(DEFUN RANDOM$ (LIMIT STATE)
       ((LAMBDA (MV LIMIT)
                ((LAMBDA (ERP VAL STATE LIMIT)
                         (CONS (IF (IF (NULL ERP)
                                       (IF (NATP VAL) (< VAL LIMIT) 'NIL)
                                       'NIL)
                                   VAL '0)
                               (CONS STATE 'NIL)))
                 (MV-NTH '0 MV)
                 (MV-NTH '1 MV)
                 (MV-NTH '2 MV)
                 LIMIT))
        (READ-ACL2-ORACLE STATE)
        LIMIT))

(DEFTHM NATP-RANDOM$ (NATP (CAR (RANDOM$ N STATE))))

(DEFTHM RANDOM$-LINEAR
        (IF (NOT (< (CAR (RANDOM$ N STATE)) '0))
            (IMPLIES (POSP N)
                     (< (CAR (RANDOM$ N STATE)) N))
            'NIL))

(DEFTHM LEN-UPDATE-NTH
        (EQUAL (LEN (UPDATE-NTH N VAL X))
               (MAX (BINARY-+ '1 (NFIX N)) (LEN X))))

(DEFTHM UPDATE-ACL2-ORACLE-PRESERVES-STATE-P1
        (IMPLIES (IF (STATE-P1 STATE)
                     (TRUE-LISTP X)
                     'NIL)
                 (STATE-P1 (UPDATE-ACL2-ORACLE X STATE))))

(DEFTHM READ-RUN-TIME-PRESERVES-STATE-P1
        (IMPLIES (STATE-P1 STATE)
                 (STATE-P1 (NTH '1 (READ-RUN-TIME STATE)))))

(DEFTHM READ-ACL2-ORACLE-PRESERVES-STATE-P1
        (IMPLIES (STATE-P1 STATE)
                 (STATE-P1 (NTH '2 (READ-ACL2-ORACLE STATE)))))

(DEFTHM NTH-0-READ-RUN-TIME-TYPE-PRESCRIPTION
        (IMPLIES (STATE-P1 STATE)
                 (RATIONALP (NTH '0 (READ-RUN-TIME STATE)))))

(DEFUN
 MAIN-TIMER (STATE)
 ((LAMBDA
    (MV)
    ((LAMBDA
          (CURRENT-TIME STATE)
          ((LAMBDA (OLD-VALUE STATE CURRENT-TIME)
                   ((LAMBDA (STATE OLD-VALUE CURRENT-TIME)
                            (CONS (BINARY-+ CURRENT-TIME (UNARY-- OLD-VALUE))
                                  (CONS STATE 'NIL)))
                    (PUT-GLOBAL 'MAIN-TIMER
                                CURRENT-TIME STATE)
                    OLD-VALUE CURRENT-TIME))
           (IF (IF (BOUNDP-GLOBAL 'MAIN-TIMER STATE)
                   (RATIONALP (GET-GLOBAL 'MAIN-TIMER STATE))
                   'NIL)
               (GET-GLOBAL 'MAIN-TIMER STATE)
               '0)
           STATE CURRENT-TIME))
     (MV-NTH '0 MV)
     (MV-NTH '1 MV)))
  (READ-RUN-TIME STATE)))

(DEFUN PUT-ASSOC-EQ (NAME VAL ALIST)
       (IF (ENDP ALIST)
           (CONS (CONS NAME VAL) 'NIL)
           (IF (EQ NAME (CAR (CAR ALIST)))
               (CONS (CONS NAME VAL) (CDR ALIST))
               (CONS (CAR ALIST)
                     (PUT-ASSOC-EQ NAME VAL (CDR ALIST))))))

(DEFUN PUT-ASSOC-EQL (NAME VAL ALIST)
       (IF (ENDP ALIST)
           (CONS (CONS NAME VAL) 'NIL)
           (IF (EQL NAME (CAR (CAR ALIST)))
               (CONS (CONS NAME VAL) (CDR ALIST))
               (CONS (CAR ALIST)
                     (PUT-ASSOC-EQL NAME VAL (CDR ALIST))))))

(DEFUN PUT-ASSOC-EQUAL (NAME VAL ALIST)
       (IF (ENDP ALIST)
           (CONS (CONS NAME VAL) 'NIL)
           (IF (EQUAL NAME (CAR (CAR ALIST)))
               (CONS (CONS NAME VAL) (CDR ALIST))
               (CONS (CAR ALIST)
                     (PUT-ASSOC-EQUAL NAME VAL (CDR ALIST))))))

(DEFUN SET-TIMER (NAME VAL STATE)
       (PUT-GLOBAL 'TIMER-ALIST
                   (PUT-ASSOC-EQ NAME
                                 VAL (GET-GLOBAL 'TIMER-ALIST STATE))
                   STATE))

(DEFUN GET-TIMER (NAME STATE)
       (CDR (ASSOC-EQ NAME (GET-GLOBAL 'TIMER-ALIST STATE))))

(DEFUN PUSH-TIMER (NAME VAL STATE)
       (SET-TIMER NAME (CONS VAL (GET-TIMER NAME STATE))
                  STATE))

(DEFTHM RATIONALP-+
        (IMPLIES (IF (RATIONALP X) (RATIONALP Y) 'NIL)
                 (RATIONALP (BINARY-+ X Y))))

(DEFTHM RATIONALP-*
        (IMPLIES (IF (RATIONALP X) (RATIONALP Y) 'NIL)
                 (RATIONALP (BINARY-* X Y))))

(DEFTHM RATIONALP-UNARY-- (IMPLIES (RATIONALP X) (RATIONALP (UNARY-- X))))

(DEFTHM RATIONALP-UNARY-/ (IMPLIES (RATIONALP X) (RATIONALP (UNARY-/ X))))

(DEFTHM RATIONALP-IMPLIES-ACL2-NUMBERP
        (IMPLIES (RATIONALP X)
                 (ACL2-NUMBERP X)))

(DEFUN POP-TIMER (NAME FLG STATE)
       ((LAMBDA (TIMER STATE FLG NAME)
                (SET-TIMER NAME
                           (IF FLG
                               (CONS (BINARY-+ (CAR TIMER) (CAR (CDR TIMER)))
                                     (CDR (CDR TIMER)))
                               (CDR TIMER))
                           STATE))
        (GET-TIMER NAME STATE)
        STATE FLG NAME))

(DEFUN ADD-TIMERS (NAME1 NAME2 STATE)
       ((LAMBDA (TIMER1 TIMER2 STATE NAME1)
                (SET-TIMER NAME1
                           (CONS (BINARY-+ (CAR TIMER1) (CAR TIMER2))
                                 (CDR TIMER1))
                           STATE))
        (GET-TIMER NAME1 STATE)
        (GET-TIMER NAME2 STATE)
        STATE NAME1))

(DEFTHM NTH-0-CONS (EQUAL (NTH '0 (CONS A L)) A))

(DEFTHM NTH-ADD1
        (IMPLIES (IF (INTEGERP N) (NOT (< N '0)) 'NIL)
                 (EQUAL (NTH (BINARY-+ '1 N) (CONS A L))
                        (NTH N L))))

(DEFTHM MAIN-TIMER-TYPE-PRESCRIPTION
        (IMPLIES (STATE-P1 STATE)
                 (IF (CONSP (MAIN-TIMER STATE))
                     (TRUE-LISTP (MAIN-TIMER STATE))
                     'NIL)))

(DEFTHM ORDERED-SYMBOL-ALISTP-ADD-PAIR-FORWARD
        (IMPLIES (IF (SYMBOLP KEY)
                     (ORDERED-SYMBOL-ALISTP L)
                     'NIL)
                 (ORDERED-SYMBOL-ALISTP (ADD-PAIR KEY VALUE L))))

(DEFTHM ASSOC-ADD-PAIR
        (IMPLIES (IF (SYMBOLP SYM2)
                     (ORDERED-SYMBOL-ALISTP ALIST)
                     'NIL)
                 (EQUAL (ASSOC SYM1 (ADD-PAIR SYM2 VAL ALIST))
                        (IF (EQUAL SYM1 SYM2)
                            (CONS SYM1 VAL)
                            (ASSOC SYM1 ALIST)))))

(DEFTHM ADD-PAIR-PRESERVES-ALL-BOUNDP
        (IMPLIES (IF (EQLABLE-ALISTP ALIST1)
                     (IF (ORDERED-SYMBOL-ALISTP ALIST2)
                         (IF (ALL-BOUNDP ALIST1 ALIST2)
                             (SYMBOLP SYM)
                             'NIL)
                         'NIL)
                     'NIL)
                 (ALL-BOUNDP ALIST1 (ADD-PAIR SYM VAL ALIST2))))

(DEFTHM STATE-P1-UPDATE-MAIN-TIMER
        (IMPLIES (STATE-P1 STATE)
                 (STATE-P1 (UPDATE-NTH '2
                                       (ADD-PAIR 'MAIN-TIMER
                                                 VAL (NTH '2 STATE))
                                       STATE))))

(DEFUN
   INCREMENT-TIMER (NAME STATE)
   ((LAMBDA (TIMER NAME STATE)
            ((LAMBDA (MV TIMER NAME)
                     ((LAMBDA (EPSILON STATE TIMER NAME)
                              (SET-TIMER NAME
                                         (CONS (BINARY-+ (CAR TIMER) EPSILON)
                                               (CDR TIMER))
                                         STATE))
                      (MV-NTH '0 MV)
                      (MV-NTH '1 MV)
                      TIMER NAME))
             (MAIN-TIMER STATE)
             TIMER NAME))
    (GET-TIMER NAME STATE)
    NAME STATE))

(DEFUN
 PRINT-RATIONAL-AS-DECIMAL
 (X CHANNEL STATE)
 ((LAMBDA
   (X00 STATE CHANNEL X)
   ((LAMBDA (STATE CHANNEL X00)
            ((LAMBDA (STATE X00 CHANNEL)
                     ((LAMBDA (STATE CHANNEL X00)
                              ((LAMBDA (R STATE CHANNEL)
                                       (IF (< R '10)
                                           ((LAMBDA (STATE CHANNEL R)
                                                    (PRINC$ R CHANNEL STATE))
                                            (PRINC$ '"0" CHANNEL STATE)
                                            CHANNEL R)
                                           (PRINC$ R CHANNEL STATE)))
                               (REM X00 '100)
                               STATE CHANNEL))
                      (PRINC$ '"." CHANNEL STATE)
                      CHANNEL X00))
             (IF (< '99 X00)
                 (PRINC$ (FLOOR (BINARY-* X00 (UNARY-/ '100)) '1)
                         CHANNEL STATE)
                 (PRINC$ '"0" CHANNEL STATE))
             X00 CHANNEL))
    (IF (< X '0)
        (PRINC$ '"-" CHANNEL STATE)
        STATE)
    CHANNEL X00))
  (ROUND (BINARY-* '100 (ABS X)) '1)
  STATE CHANNEL X))

(DEFUN PRINT-TIMER (NAME CHANNEL STATE)
       (PRINT-RATIONAL-AS-DECIMAL (CAR (GET-TIMER NAME STATE))
                                  CHANNEL STATE))

(DEFUN
 PRIN1$ (X CHANNEL STATE)
 (IF
  (ACL2-NUMBERP X)
  (PRINC$ X CHANNEL STATE)
  (IF
   (CHARACTERP X)
   ((LAMBDA (STATE CHANNEL X)
            (PRINC$ (IF (EQL X '#\Newline)
                        '"Newline"
                        (IF (EQL X '#\Space)
                            '"Space"
                            (IF (EQL X '#\Page)
                                '"Page"
                                (IF (EQL X '#\Tab)
                                    '"Tab"
                                    (IF (EQL X '#\Rubout) '"Rubout" X)))))
                    CHANNEL STATE))
    (PRINC$ '"#\\" CHANNEL STATE)
    CHANNEL X)
   (IF
    (STRINGP X)
    ((LAMBDA (L X STATE CHANNEL)
             ((LAMBDA (STATE CHANNEL X L)
                      ((LAMBDA (STATE CHANNEL)
                               (PRINC$ '#\" CHANNEL STATE))
                       (IF (IF (MEMBER '#\\ L)
                               (MEMBER '#\\ L)
                               (MEMBER '#\" L))
                           (PRIN1-WITH-SLASHES X '#\"
                                               CHANNEL STATE)
                           (PRINC$ X CHANNEL STATE))
                       CHANNEL))
              (PRINC$ '#\" CHANNEL STATE)
              CHANNEL X L))
     (COERCE X 'LIST)
     X STATE CHANNEL)
    ((LAMBDA (STATE CHANNEL X)
             (IF (NEEDS-SLASHES (SYMBOL-NAME X) STATE)
                 ((LAMBDA (STATE CHANNEL X)
                          ((LAMBDA (STATE CHANNEL)
                                   (PRINC$ '#\| CHANNEL STATE))
                           (PRIN1-WITH-SLASHES (SYMBOL-NAME X)
                                               '#\|
                                               CHANNEL STATE)
                           CHANNEL))
                  (PRINC$ '#\| CHANNEL STATE)
                  CHANNEL X)
                 (PRINC$ X CHANNEL STATE)))
     (IF
      (KEYWORDP X)
      (PRINC$ '#\: CHANNEL STATE)
      (IF
       (IF
        (EQUAL (SYMBOL-PACKAGE-NAME X)
               (GET-GLOBAL 'CURRENT-PACKAGE STATE))
        (EQUAL (SYMBOL-PACKAGE-NAME X)
               (GET-GLOBAL 'CURRENT-PACKAGE STATE))
        (MEMBER-EQ
           X
           (CAR (CDR (ASSOC-EQUAL (GET-GLOBAL 'CURRENT-PACKAGE STATE)
                                  (GLOBAL-VAL 'KNOWN-PACKAGE-ALIST
                                              (GET-GLOBAL 'CURRENT-ACL2-WORLD
                                                          STATE)))))))
       STATE
       ((LAMBDA (P CHANNEL STATE)
                ((LAMBDA (STATE CHANNEL)
                         (PRINC$ '"::" CHANNEL STATE))
                 (IF (NEEDS-SLASHES P STATE)
                     ((LAMBDA (STATE CHANNEL P)
                              ((LAMBDA (STATE CHANNEL)
                                       (PRINC$ '#\| CHANNEL STATE))
                               (PRIN1-WITH-SLASHES P '#\|
                                                   CHANNEL STATE)
                               CHANNEL))
                      (PRINC$ '#\| CHANNEL STATE)
                      CHANNEL P)
                     (IF (EQ (GET-GLOBAL 'PRINT-CASE STATE)
                             ':DOWNCASE)
                         (PRINC$ (STRING-DOWNCASE P)
                                 CHANNEL STATE)
                         (PRINC$ P CHANNEL STATE)))
                 CHANNEL))
        (SYMBOL-PACKAGE-NAME X)
        CHANNEL STATE)))
     CHANNEL X)))))

(DEFTHM ALL-BOUNDP-PRESERVES-ASSOC
        (IMPLIES (IF (EQLABLE-ALISTP TBL1)
                     (IF (EQLABLE-ALISTP TBL2)
                         (IF (ALL-BOUNDP TBL1 TBL2)
                             (IF (SYMBOLP X) (ASSOC-EQ X TBL1) 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 (ASSOC X TBL2)))

(DEFUN W (STATE) (GET-GLOBAL 'CURRENT-ACL2-WORLD STATE))

(DEFUN CURRENT-PACKAGE (STATE) (GET-GLOBAL 'CURRENT-PACKAGE STATE))

(DEFUN KNOWN-PACKAGE-ALIST (STATE)
       (FGETPROP 'KNOWN-PACKAGE-ALIST
                 'GLOBAL-VALUE
                 'NIL
                 (W STATE)))

(DEFTHM
    STATE-P1-UPDATE-NTH-2-WORLD
    (IMPLIES (IF (STATE-P1 STATE)
                 (IF (WORLDP WRLD)
                     (IF (KNOWN-PACKAGE-ALISTP (FGETPROP 'KNOWN-PACKAGE-ALIST
                                                         'GLOBAL-VALUE
                                                         'NIL
                                                         WRLD))
                         (SYMBOL-ALISTP (FGETPROP 'ACL2-DEFAULTS-TABLE
                                                  'TABLE-ALIST
                                                  'NIL
                                                  WRLD))
                         'NIL)
                     'NIL)
                 'NIL)
             (STATE-P1 (UPDATE-NTH '2
                                   (ADD-PAIR 'CURRENT-ACL2-WORLD
                                             WRLD (NTH '2 STATE))
                                   STATE))))

(DEFTHM TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP-ASSOC-EQUAL
        (IMPLIES (TRUE-LIST-LISTP L)
                 (TRUE-LISTP (ASSOC-EQUAL KEY L))))

(DEFUN UNION-EQ (LST1 LST2)
       (IF (ENDP LST1)
           LST2
           (IF (MEMBER-EQ (CAR LST1) LST2)
               (UNION-EQ (CDR LST1) LST2)
               (CONS (CAR LST1)
                     (UNION-EQ (CDR LST1) LST2)))))

(DEFUN LD-SKIP-PROOFSP (STATE) (GET-GLOBAL 'LD-SKIP-PROOFSP STATE))

(DEFUN
 MAKE-VAR-LST1 (ROOT SYM N ACC)
 (IF
  (ZP N)
  ACC
  (MAKE-VAR-LST1
   ROOT SYM (BINARY-+ '-1 N)
   (CONS
    (INTERN-IN-PACKAGE-OF-SYMBOL
         (COERCE (BINARY-APPEND ROOT
                                (EXPLODE-NONNEGATIVE-INTEGER (BINARY-+ '-1 N)
                                                             '10
                                                             'NIL))
                 'STRING)
         SYM)
    ACC))))

(DEFUN MAKE-VAR-LST (SYM N)
       (MAKE-VAR-LST1 (COERCE (SYMBOL-NAME SYM) 'LIST)
                      SYM N 'NIL))

(DEFUN NON-FREE-VAR-RUNES
       (RUNES FREE-VAR-RUNES-ONCE
              FREE-VAR-RUNES-ALL ACC)
       (IF (ENDP RUNES)
           ACC
           (NON-FREE-VAR-RUNES (CDR RUNES)
                               FREE-VAR-RUNES-ONCE FREE-VAR-RUNES-ALL
                               (IF (IF (MEMBER-EQUAL (CAR RUNES)
                                                     FREE-VAR-RUNES-ONCE)
                                       (MEMBER-EQUAL (CAR RUNES)
                                                     FREE-VAR-RUNES-ONCE)
                                       (MEMBER-EQUAL (CAR RUNES)
                                                     FREE-VAR-RUNES-ALL))
                                   ACC (CONS (CAR RUNES) ACC)))))

(DEFUN FREE-VAR-RUNES (FLG WRLD)
       (IF (EQ FLG ':ONCE)
           (GLOBAL-VAL 'FREE-VAR-RUNES-ONCE WRLD)
           (GLOBAL-VAL 'FREE-VAR-RUNES-ALL WRLD)))

(DEFTHM NATP-POSITION-AC
        (IMPLIES (IF (INTEGERP ACC)
                     (NOT (< ACC '0))
                     'NIL)
                 (IF (EQUAL (POSITION-AC ITEM LST ACC) 'NIL)
                     (EQUAL (POSITION-AC ITEM LST ACC) 'NIL)
                     (IF (INTEGERP (POSITION-AC ITEM LST ACC))
                         (NOT (< (POSITION-AC ITEM LST ACC) '0))
                         'NIL))))

(DEFUN
 ABSOLUTE-PATHNAME-STRING-P
 (STR DIRECTORYP OS)
 ((LAMBDA
   (LEN DIRECTORYP STR OS)
   (IF
    (< '0 LEN)
    (IF
     (IF
      (EQ OS ':MSWINDOWS)
      ((LAMBDA (POS-COLON POS-SEP)
               (IF POS-COLON
                   (IF POS-SEP (< POS-COLON POS-SEP) 'NIL)
                   'NIL))
       (POSITION '#\: STR)
       (POSITION '#\/ STR))
      (IF
       (EQL (CHAR STR '0) '#\/)
       'T
       (IF
        (EQL (CHAR STR '0) '#\~)
        (PROG2$
         (IF
          (IF (EQL '1 LEN)
              (EQL '1 LEN)
              (EQL (CHAR STR '1) '#\/))
          (HARD-ERROR
           'ABSOLUTE-PATHNAME-STRING-P
           '"Implementation error: Forgot ~
                                               to apply ~
                                               expand-tilde-to-user-home-dir ~
                                               before calling ~
                                               absolute-pathname-string-p. ~
                                               Please contact the ACL2 ~
                                               implementors."
           'NIL)
          'NIL)
         'T)
        'NIL)))
     (IF DIRECTORYP
         (EQL (CHAR STR (BINARY-+ '-1 LEN)) '#\/)
         'T)
     'NIL)
    'NIL))
  (LENGTH STR)
  DIRECTORYP STR OS))

(DEFUN OS (WRLD) (GLOBAL-VAL 'OPERATING-SYSTEM WRLD))

(DEFUN INCLUDE-BOOK-DIR-ALISTP (X OS)
       (IF (ATOM X)
           (NULL X)
           (IF (CONSP (CAR X))
               (IF (KEYWORDP (CAR (CAR X)))
                   (IF (STRINGP (CDR (CAR X)))
                       (IF (ABSOLUTE-PATHNAME-STRING-P (CDR (CAR X))
                                                       'T
                                                       OS)
                           (INCLUDE-BOOK-DIR-ALISTP (CDR X) OS)
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)))

(DEFUN LEGAL-RULER-EXTENDERS-P (X)
       (IF (ATOM X)
           (NULL X)
           (IF (KEYWORDP (CAR X))
               (IF (EQ (CAR X) ':LAMBDAS)
                   (LEGAL-RULER-EXTENDERS-P (CDR X))
                   'NIL)
               (IF (SYMBOLP (CAR X))
                   (LEGAL-RULER-EXTENDERS-P (CDR X))
                   'NIL))))

(DEFUN TABLE-ALIST (NAME WRLD) (FGETPROP NAME 'TABLE-ALIST 'NIL WRLD))

(DEFUN DEFAULT-VERIFY-GUARDS-EAGERNESS (WRLD)
       (IF (CDR (ASSOC-EQ ':VERIFY-GUARDS-EAGERNESS
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           (CDR (ASSOC-EQ ':VERIFY-GUARDS-EAGERNESS
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           '1))

(DEFUN DEFAULT-COMPILE-FNS (WRLD)
       (CDR (ASSOC-EQ ':COMPILE-FNS
                      (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                   WRLD))))

(DEFUN DEFAULT-MEASURE-FUNCTION (WRLD)
       (IF (CDR (ASSOC-EQ ':MEASURE-FUNCTION
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           (CDR (ASSOC-EQ ':MEASURE-FUNCTION
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           'ACL2-COUNT))

(DEFUN DEFAULT-WELL-FOUNDED-RELATION (WRLD)
       (IF (CDR (ASSOC-EQ ':WELL-FOUNDED-RELATION
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           (CDR (ASSOC-EQ ':WELL-FOUNDED-RELATION
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           'O<))

(DEFUN GOOD-DEFUN-MODE-P (P) (MEMBER-EQ P '(:LOGIC :PROGRAM)))

(DEFUN DEFAULT-DEFUN-MODE (WRLD)
       ((LAMBDA (VAL)
                (IF (GOOD-DEFUN-MODE-P VAL)
                    VAL ':PROGRAM))
        (CDR (ASSOC-EQ ':DEFUN-MODE
                       (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                    WRLD)))))

(DEFUN DEFAULT-DEFUN-MODE-FROM-STATE (STATE) (DEFAULT-DEFUN-MODE (W STATE)))

(DEFUN INVISIBLE-FNS-TABLE (WRLD) (TABLE-ALIST 'INVISIBLE-FNS-TABLE WRLD))

(DEFUN UNARY-FUNCTION-SYMBOL-LISTP (LST WRLD)
       (IF (ATOM LST)
           (NULL LST)
           (IF (SYMBOLP (CAR LST))
               (IF ((LAMBDA (FORMALS)
                            (IF (CONSP FORMALS)
                                (NULL (CDR FORMALS))
                                'NIL))
                    (FGETPROP (CAR LST) 'FORMALS 'NIL WRLD))
                   (UNARY-FUNCTION-SYMBOL-LISTP (CDR LST)
                                                WRLD)
                   'NIL)
               'NIL)))

(DEFUN INVISIBLE-FNS-ENTRYP (KEY VAL WRLD)
       (IF (SYMBOLP KEY)
           (IF (FUNCTION-SYMBOLP KEY WRLD)
               (UNARY-FUNCTION-SYMBOL-LISTP VAL WRLD)
               'NIL)
           'NIL))

(DEFUN DELETE-ASSOC-EQ (KEY ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQ KEY (CAR (CAR ALIST)))
               (CDR ALIST)
               (CONS (CAR ALIST)
                     (DELETE-ASSOC-EQ KEY (CDR ALIST))))))

(DEFUN DELETE-ASSOC-EQUAL (KEY ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQUAL KEY (CAR (CAR ALIST)))
               (CDR ALIST)
               (CONS (CAR ALIST)
                     (DELETE-ASSOC-EQUAL KEY (CDR ALIST))))))

(DEFUN BACKCHAIN-LIMIT (WRLD)
       (IF (CDR (ASSOC-EQ ':BACKCHAIN-LIMIT
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           (CDR (ASSOC-EQ ':BACKCHAIN-LIMIT
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           'NIL))

(DEFUN DEFAULT-BACKCHAIN-LIMIT (WRLD)
       (IF (CDR (ASSOC-EQ ':DEFAULT-BACKCHAIN-LIMIT
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           (CDR (ASSOC-EQ ':DEFAULT-BACKCHAIN-LIMIT
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           'NIL))

(DEFUN REWRITE-STACK-LIMIT (WRLD)
       (IF (CDR (ASSOC-EQ ':REWRITE-STACK-LIMIT
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           (CDR (ASSOC-EQ ':REWRITE-STACK-LIMIT
                          (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                       WRLD)))
           '1000))

(DEFUN CASE-SPLIT-LIMITATIONS (WRLD)
       (CDR (ASSOC-EQ ':CASE-SPLIT-LIMITATIONS
                      (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                   WRLD))))

(DEFUN BINOP-TABLE (WRLD) (TABLE-ALIST 'BINOP-TABLE WRLD))

(DEFUN MATCH-FREE-DEFAULT (WRLD)
       (CDR (ASSOC-EQ ':MATCH-FREE-DEFAULT
                      (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                   WRLD))))

(DEFUN MATCH-FREE-OVERRIDE (WRLD)
       ((LAMBDA (PAIR WRLD)
                (IF (IF (NULL PAIR)
                        (NULL PAIR)
                        (EQ (CDR PAIR) ':CLEAR))
                    ':CLEAR
                    (CONS (CDR (ASSOC-EQ ':MATCH-FREE-OVERRIDE-NUME
                                         (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                                                      WRLD)))
                          (CDR PAIR))))
        (ASSOC-EQ ':MATCH-FREE-OVERRIDE
                  (TABLE-ALIST 'ACL2-DEFAULTS-TABLE WRLD))
        WRLD))

(DEFUN NON-LINEARP (WRLD)
       ((LAMBDA (TEMP)
                (IF TEMP (CDR TEMP) 'NIL))
        (ASSOC-EQ ':NON-LINEARP
                  (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
                               WRLD))))

(DEFUN MACRO-ALIASES (WRLD) (TABLE-ALIST 'MACRO-ALIASES-TABLE WRLD))

(DEFUN NTH-ALIASES (WRLD) (TABLE-ALIST 'NTH-ALIASES-TABLE WRLD))

(DEFUN DEFAULT-HINTS (WRLD)
       (CDR (ASSOC-EQ 'T
                      (TABLE-ALIST 'DEFAULT-HINTS-TABLE
                                   WRLD))))

(DEFUN FIX-TRUE-LIST (X)
       (IF (CONSP X)
           (CONS (CAR X) (FIX-TRUE-LIST (CDR X)))
           'NIL))

(DEFTHM PAIRLIS$-FIX-TRUE-LIST
        (EQUAL (PAIRLIS$ X (FIX-TRUE-LIST Y))
               (PAIRLIS$ X Y)))

(DEFUN BOOLEAN-LISTP (LST)
       (IF (ATOM LST)
           (EQ LST 'NIL)
           (IF (IF (EQ (CAR LST) 'T)
                   (EQ (CAR LST) 'T)
                   (EQ (CAR LST) 'NIL))
               (BOOLEAN-LISTP (CDR LST))
               'NIL)))

(DEFTHM BOOLEAN-LISTP-CONS
        (EQUAL (BOOLEAN-LISTP (CONS X Y))
               (IF (BOOLEANP X)
                   (BOOLEAN-LISTP Y)
                   'NIL)))

(DEFTHM BOOLEAN-LISTP-FORWARD
        (IMPLIES (BOOLEAN-LISTP (CONS A LST))
                 (IF (BOOLEANP A)
                     (BOOLEAN-LISTP LST)
                     'NIL)))

(DEFTHM BOOLEAN-LISTP-FORWARD-TO-SYMBOL-LISTP
        (IMPLIES (BOOLEAN-LISTP X)
                 (SYMBOL-LISTP X)))

(DEFAXIOM COMPLETION-OF-+
          (EQUAL (BINARY-+ X Y)
                 (IF (ACL2-NUMBERP X)
                     (IF (ACL2-NUMBERP Y) (BINARY-+ X Y) X)
                     (IF (ACL2-NUMBERP Y) Y '0))))

(DEFTHM DEFAULT-+-1
        (IMPLIES (NOT (ACL2-NUMBERP X))
                 (EQUAL (BINARY-+ X Y) (FIX Y))))

(DEFTHM DEFAULT-+-2
        (IMPLIES (NOT (ACL2-NUMBERP Y))
                 (EQUAL (BINARY-+ X Y) (FIX X))))

(DEFAXIOM COMPLETION-OF-*
          (EQUAL (BINARY-* X Y)
                 (IF (ACL2-NUMBERP X)
                     (IF (ACL2-NUMBERP Y) (BINARY-* X Y) '0)
                     '0)))

(DEFTHM DEFAULT-*-1
        (IMPLIES (NOT (ACL2-NUMBERP X))
                 (EQUAL (BINARY-* X Y) '0)))

(DEFTHM DEFAULT-*-2
        (IMPLIES (NOT (ACL2-NUMBERP Y))
                 (EQUAL (BINARY-* X Y) '0)))

(DEFAXIOM COMPLETION-OF-UNARY-MINUS
          (EQUAL (UNARY-- X)
                 (IF (ACL2-NUMBERP X) (UNARY-- X) '0)))

(DEFTHM DEFAULT-UNARY-MINUS
        (IMPLIES (NOT (ACL2-NUMBERP X))
                 (EQUAL (UNARY-- X) '0)))

(DEFAXIOM COMPLETION-OF-UNARY-/
          (EQUAL (UNARY-/ X)
                 (IF (IF (ACL2-NUMBERP X)
                         (NOT (EQUAL X '0))
                         'NIL)
                     (UNARY-/ X)
                     '0)))

(DEFTHM DEFAULT-UNARY-/
        (IMPLIES (IF (NOT (ACL2-NUMBERP X))
                     (NOT (ACL2-NUMBERP X))
                     (EQUAL X '0))
                 (EQUAL (UNARY-/ X) '0)))

(DEFAXIOM COMPLETION-OF-<
          (EQUAL (< X Y)
                 (IF (IF (RATIONALP X) (RATIONALP Y) 'NIL)
                     (< X Y)
                     ((LAMBDA (X1 Y1)
                              (IF (< (REALPART X1) (REALPART Y1))
                                  (< (REALPART X1) (REALPART Y1))
                                  (IF (EQUAL (REALPART X1) (REALPART Y1))
                                      (< (IMAGPART X1) (IMAGPART Y1))
                                      'NIL)))
                      (IF (ACL2-NUMBERP X) X '0)
                      (IF (ACL2-NUMBERP Y) Y '0)))))

(DEFTHM DEFAULT-<-1
        (IMPLIES (NOT (ACL2-NUMBERP X))
                 (EQUAL (< X Y) (< '0 Y))))

(DEFTHM DEFAULT-<-2
        (IMPLIES (NOT (ACL2-NUMBERP Y))
                 (EQUAL (< X Y) (< X '0))))

(DEFAXIOM COMPLETION-OF-CAR (EQUAL (CAR X) (IF (CONSP X) (CAR X) 'NIL)))

(DEFTHM DEFAULT-CAR (IMPLIES (NOT (CONSP X)) (EQUAL (CAR X) 'NIL)))

(DEFAXIOM COMPLETION-OF-CDR (EQUAL (CDR X) (IF (CONSP X) (CDR X) 'NIL)))

(DEFTHM DEFAULT-CDR (IMPLIES (NOT (CONSP X)) (EQUAL (CDR X) 'NIL)))

(DEFTHM CONS-CAR-CDR
        (EQUAL (CONS (CAR X) (CDR X))
               (IF (CONSP X) X (CONS 'NIL 'NIL))))

(DEFAXIOM COMPLETION-OF-CHAR-CODE
          (EQUAL (CHAR-CODE X)
                 (IF (CHARACTERP X) (CHAR-CODE X) '0)))

(DEFTHM DEFAULT-CHAR-CODE
        (IMPLIES (NOT (CHARACTERP X))
                 (EQUAL (CHAR-CODE X) '0)))

(DEFAXIOM COMPLETION-OF-CODE-CHAR
          (EQUAL (CODE-CHAR X)
                 (IF (IF (INTEGERP X)
                         (IF (NOT (< X '0)) (< X '256) 'NIL)
                         'NIL)
                     (CODE-CHAR X)
                     (CODE-CHAR '0))))

(DEFAXIOM COMPLETION-OF-COMPLEX
          (EQUAL (COMPLEX X Y)
                 (COMPLEX (IF (RATIONALP X) X '0)
                          (IF (RATIONALP Y) Y '0))))

(DEFTHM DEFAULT-COMPLEX-1
        (IMPLIES (NOT (RATIONALP X))
                 (EQUAL (COMPLEX X Y) (COMPLEX '0 Y))))

(DEFTHM DEFAULT-COMPLEX-2
        (IMPLIES (NOT (RATIONALP Y))
                 (EQUAL (COMPLEX X Y)
                        (IF (RATIONALP X) X '0))))

(DEFTHM COMPLEX-0 (EQUAL (COMPLEX X '0) (RFIX X)))

(DEFTHM ADD-DEF-COMPLEX
        (EQUAL (BINARY-+ X Y)
               (COMPLEX (BINARY-+ (REALPART X) (REALPART Y))
                        (BINARY-+ (IMAGPART X) (IMAGPART Y)))))

(DEFTHM REALPART-+
        (EQUAL (REALPART (BINARY-+ X Y))
               (BINARY-+ (REALPART X) (REALPART Y))))

(DEFTHM IMAGPART-+
        (EQUAL (IMAGPART (BINARY-+ X Y))
               (BINARY-+ (IMAGPART X) (IMAGPART Y))))

(DEFAXIOM COMPLETION-OF-COERCE
          (EQUAL (COERCE X Y)
                 (IF (EQUAL Y 'LIST)
                     (IF (STRINGP X) (COERCE X 'LIST) 'NIL)
                     (COERCE (MAKE-CHARACTER-LIST X)
                             'STRING))))

(DEFTHM DEFAULT-COERCE-1
        (IMPLIES (NOT (STRINGP X))
                 (EQUAL (COERCE X 'LIST) 'NIL)))

(DEFTHM MAKE-CHARACTER-LIST-MAKE-CHARACTER-LIST
        (EQUAL (MAKE-CHARACTER-LIST (MAKE-CHARACTER-LIST X))
               (MAKE-CHARACTER-LIST X)))

(DEFTHM DEFAULT-COERCE-2
        (IMPLIES (IF (SYNP 'NIL
                           '(SYNTAXP (NOT (EQUAL Y ''STRING)))
                           '(IF (NOT (EQUAL Y ''STRING)) 'T 'NIL))
                     (NOT (EQUAL Y 'LIST))
                     'NIL)
                 (EQUAL (COERCE X Y)
                        (COERCE X 'STRING))))

(DEFTHM DEFAULT-COERCE-3
        (IMPLIES (NOT (CONSP X))
                 (EQUAL (COERCE X 'STRING) '"")))

(DEFAXIOM COMPLETION-OF-DENOMINATOR
          (EQUAL (DENOMINATOR X)
                 (IF (RATIONALP X) (DENOMINATOR X) '1)))

(DEFTHM DEFAULT-DENOMINATOR
        (IMPLIES (NOT (RATIONALP X))
                 (EQUAL (DENOMINATOR X) '1)))

(DEFAXIOM COMPLETION-OF-IMAGPART
          (EQUAL (IMAGPART X)
                 (IF (ACL2-NUMBERP X) (IMAGPART X) '0)))

(DEFTHM DEFAULT-IMAGPART
        (IMPLIES (NOT (ACL2-NUMBERP X))
                 (EQUAL (IMAGPART X) '0)))

(DEFAXIOM COMPLETION-OF-INTERN-IN-PACKAGE-OF-SYMBOL
          (EQUAL (INTERN-IN-PACKAGE-OF-SYMBOL X Y)
                 (IF (IF (STRINGP X) (SYMBOLP Y) 'NIL)
                     (INTERN-IN-PACKAGE-OF-SYMBOL X Y)
                     'NIL)))

(DEFAXIOM COMPLETION-OF-NUMERATOR
          (EQUAL (NUMERATOR X)
                 (IF (RATIONALP X) (NUMERATOR X) '0)))

(DEFTHM DEFAULT-NUMERATOR
        (IMPLIES (NOT (RATIONALP X))
                 (EQUAL (NUMERATOR X) '0)))

(DEFAXIOM COMPLETION-OF-REALPART
          (EQUAL (REALPART X)
                 (IF (ACL2-NUMBERP X) (REALPART X) '0)))

(DEFTHM DEFAULT-REALPART
        (IMPLIES (NOT (ACL2-NUMBERP X))
                 (EQUAL (REALPART X) '0)))

(DEFAXIOM COMPLETION-OF-SYMBOL-NAME
          (EQUAL (SYMBOL-NAME X)
                 (IF (SYMBOLP X) (SYMBOL-NAME X) '"")))

(DEFTHM DEFAULT-SYMBOL-NAME
        (IMPLIES (NOT (SYMBOLP X))
                 (EQUAL (SYMBOL-NAME X) '"")))

(DEFAXIOM COMPLETION-OF-SYMBOL-PACKAGE-NAME
          (EQUAL (SYMBOL-PACKAGE-NAME X)
                 (IF (SYMBOLP X)
                     (SYMBOL-PACKAGE-NAME X)
                     '"")))

(DEFTHM DEFAULT-SYMBOL-PACKAGE-NAME
        (IMPLIES (NOT (SYMBOLP X))
                 (EQUAL (SYMBOL-PACKAGE-NAME X) '"")))

(DEFUN DOUBLE-REWRITE (X) X)

(DEFUN
 WITH-PROVER-TIME-LIMIT (TIME FORM)
 (PROG2$
  (IF
   ((LAMBDA (TIME)
            (IF (RATIONALP TIME) (< '0 TIME) 'NIL))
    (IF (IF (CONSP TIME) (NULL (CDR TIME)) 'NIL)
        (CAR TIME)
        TIME))
   ((LAMBDA (TIME)
            (IF (RATIONALP TIME) (< '0 TIME) 'NIL))
    (IF (IF (CONSP TIME) (NULL (CDR TIME)) 'NIL)
        (CAR TIME)
        TIME))
   (ILLEGAL
    'WITH-PROVER-TIME-LIMIT
    '"The first argument to with-prover-time-limit must evaluate ~
                        to a non-negative rational number but that value is ~
                        ~x0."
    (CONS (CONS '#\0 TIME) 'NIL)))
  FORM))

(DEFUN TIME-LIMIT4-REACHED-P (MSG) 'NIL)

(DEFUN WORMHOLE1 (NAME INPUT FORM LD-SPECIALS) 'NIL)

(DEFUN WORMHOLE-P (STATE) (READ-ACL2-ORACLE STATE))

(DEFUN ABORT! NIL 'NIL)

(DEFUN FMT-TO-COMMENT-WINDOW (STR ALIST COL EVISC-TUPLE) 'NIL)

(DEFUN FMT-TO-COMMENT-WINDOW! (STR ALIST COL EVISC-TUPLE) 'NIL)

(DEFUN PAIRLIS2 (X Y)
       (IF (ENDP Y)
           'NIL
           (CONS (CONS (CAR X) (CAR Y))
                 (PAIRLIS2 (CDR X) (CDR Y)))))

(DEFUN DUPLICATES (LST)
       (IF (ENDP LST)
           'NIL
           (IF (MEMBER-EQ (CAR LST) (CDR LST))
               (ADD-TO-SET-EQ (CAR LST)
                              (DUPLICATES (CDR LST)))
               (DUPLICATES (CDR LST)))))

(DEFUN ADD-TO-SET-EQUAL (X L) (IF (MEMBER-EQUAL X L) L (CONS X L)))

(DEFUN INTERSECTION-EQ (L1 L2)
       (IF (ENDP L1)
           'NIL
           (IF (MEMBER-EQ (CAR L1) L2)
               (CONS (CAR L1)
                     (INTERSECTION-EQ (CDR L1) L2))
               (INTERSECTION-EQ (CDR L1) L2))))

(DEFUN EVENS (L) (IF (ENDP L) 'NIL (CONS (CAR L) (EVENS (CDR (CDR L))))))

(DEFUN ODDS (L) (EVENS (CDR L)))

(DEFUN SET-EQUALP-EQUAL (LST1 LST2)
       (IF (SUBSETP-EQUAL LST1 LST2)
           (SUBSETP-EQUAL LST2 LST1)
           'NIL))

(DEFUN
     RECORD-ERROR (NAME REC)
     (HARD-ERROR 'RECORD-ERROR
                 '"An attempt was made to treat ~x0 as a record of type ~x1."
                 (CONS (CONS '#\0 REC)
                       (CONS (CONS '#\1 NAME) 'NIL))))

(DEFUN
 RECORD-ACCESSOR-FUNCTION-NAME
 (NAME FIELD)
 (INTERN-IN-PACKAGE-OF-SYMBOL
  (COERCE
     (BINARY-APPEND
          (COERCE '"Access " 'LIST)
          (BINARY-APPEND (COERCE (SYMBOL-NAME NAME) 'LIST)
                         (BINARY-APPEND (COERCE '" record field " 'LIST)
                                        (COERCE (SYMBOL-NAME FIELD) 'LIST))))
     'STRING)
  NAME))

(DEFUN
 MFC-CLAUSE (MFC)
 (IF
  (IF
   (TRUE-LISTP MFC)
   (IF
    (TRUE-LISTP
     ((LAMBDA
           (RCNST)
           (CAR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR RCNST)))))))))))
      MFC))
    (IF
     (CONSP
      (NTH
       '4
       ((LAMBDA
           (RCNST)
           (CAR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR RCNST)))))))))))
        MFC)))
     (PSEUDO-TERM-LISTP
      ((LAMBDA (CURRENT-CLAUSE)
               (CDR (CAR (CDR (CDR (CDR (CDR CURRENT-CLAUSE)))))))
       ((LAMBDA
           (RCNST)
           (CAR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR RCNST)))))))))))
        MFC)))
     'NIL)
    'NIL)
   'NIL)
  ((LAMBDA (CURRENT-CLAUSE)
           (CDR (CAR (CDR (CDR (CDR (CDR CURRENT-CLAUSE)))))))
   ((LAMBDA
         (RCNST)
         (CAR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR (CDR RCNST)))))))))))
    MFC))
  'NIL))

(DEFUN MFC-RDEPTH (MFC)
       (IF (TRUE-LISTP MFC)
           ((LAMBDA (RDEPTH) (CAR RDEPTH)) MFC)
           'NIL))

(DEFUN TYPE-ALIST-ENTRYP (X)
       (IF (CONSP X)
           (IF (PSEUDO-TERMP (CAR X))
               (IF (CONSP (CDR X))
                   (IF (INTEGERP (CAR (CDR X)))
                       (IF (NOT (< (CAR (CDR X)) '-8192))
                           (NOT (< '8191 (CAR (CDR X))))
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL)
           'NIL))

(DEFUN TYPE-ALISTP (X)
       (IF (CONSP X)
           (IF (TYPE-ALIST-ENTRYP (CAR X))
               (TYPE-ALISTP (CDR X))
               'NIL)
           (EQ X 'NIL)))

(DEFUN MFC-TYPE-ALIST (MFC)
       (IF (IF (TRUE-LISTP MFC)
               (TYPE-ALISTP ((LAMBDA (TYPE-ALIST)
                                     (CAR (CDR TYPE-ALIST)))
                             MFC))
               'NIL)
           ((LAMBDA (TYPE-ALIST)
                    (CAR (CDR TYPE-ALIST)))
            MFC)
           'NIL))

(DEFUN
 MFC-ANCESTORS (MFC)
 (IF
  (IF
    (TRUE-LISTP MFC)
    (TRUE-LISTP ((LAMBDA (ANCESTORS)
                         (CAR (CDR (CDR (CDR (CDR (CDR (CDR ANCESTORS))))))))
                 MFC))
    'NIL)
  ((LAMBDA (ANCESTORS)
           (CAR (CDR (CDR (CDR (CDR (CDR (CDR ANCESTORS))))))))
   MFC)
  'NIL))

(DEFTHM PSEUDO-TERM-LISTP-MFC-CLAUSE (PSEUDO-TERM-LISTP (MFC-CLAUSE MFC)))

(DEFTHM TYPE-ALISTP-MFC-TYPE-ALIST (TYPE-ALISTP (MFC-TYPE-ALIST MFC)))

(DEFUN BAD-ATOM (X)
       (NOT (IF (CONSP X)
                (CONSP X)
                (IF (ACL2-NUMBERP X)
                    (ACL2-NUMBERP X)
                    (IF (SYMBOLP X)
                        (SYMBOLP X)
                        (IF (CHARACTERP X)
                            (CHARACTERP X)
                            (STRINGP X)))))))

(DEFTHM BAD-ATOM-COMPOUND-RECOGNIZER
        (IFF (BAD-ATOM X)
             (NOT (IF (CONSP X)
                      (CONSP X)
                      (IF (ACL2-NUMBERP X)
                          (ACL2-NUMBERP X)
                          (IF (SYMBOLP X)
                              (SYMBOLP X)
                              (IF (CHARACTERP X)
                                  (CHARACTERP X)
                                  (STRINGP X))))))))

(DEFAXIOM BOOLEANP-BAD-ATOM<=
          (IF (EQUAL (BAD-ATOM<= X Y) 'T)
              (EQUAL (BAD-ATOM<= X Y) 'T)
              (EQUAL (BAD-ATOM<= X Y) 'NIL)))

(DEFAXIOM BAD-ATOM<=-ANTISYMMETRIC
          (IMPLIES (IF (BAD-ATOM X)
                       (IF (BAD-ATOM Y)
                           (IF (BAD-ATOM<= X Y)
                               (BAD-ATOM<= Y X)
                               'NIL)
                           'NIL)
                       'NIL)
                   (EQUAL X Y)))

(DEFAXIOM BAD-ATOM<=-TRANSITIVE
          (IMPLIES (IF (BAD-ATOM<= X Y)
                       (IF (BAD-ATOM<= Y Z)
                           (IF (BAD-ATOM X)
                               (IF (BAD-ATOM Y) (BAD-ATOM Z) 'NIL)
                               'NIL)
                           'NIL)
                       'NIL)
                   (BAD-ATOM<= X Z)))

(DEFAXIOM BAD-ATOM<=-TOTAL
          (IMPLIES (IF (BAD-ATOM X) (BAD-ATOM Y) 'NIL)
                   (IF (BAD-ATOM<= X Y)
                       (BAD-ATOM<= X Y)
                       (BAD-ATOM<= Y X))))

(DEFUN
 ALPHORDER (X Y)
 (IF (RATIONALP X)
     (IF (RATIONALP Y) (NOT (< Y X)) 'T)
     (IF (RATIONALP Y)
         'NIL
         (IF (COMPLEX-RATIONALP X)
             (IF (COMPLEX-RATIONALP Y)
                 (IF (< (REALPART X) (REALPART Y))
                     (< (REALPART X) (REALPART Y))
                     (IF (= (REALPART X) (REALPART Y))
                         (NOT (< (IMAGPART Y) (IMAGPART X)))
                         'NIL))
                 'T)
             (IF (COMPLEX-RATIONALP Y)
                 'NIL
                 (IF (CHARACTERP X)
                     (IF (CHARACTERP Y)
                         (NOT (< (CHAR-CODE Y) (CHAR-CODE X)))
                         'T)
                     (IF (CHARACTERP Y)
                         'NIL
                         (IF (STRINGP X)
                             (IF (STRINGP Y)
                                 (IF (STRING<= X Y) 'T 'NIL)
                                 'T)
                             (IF (STRINGP Y)
                                 'NIL
                                 (IF (SYMBOLP X)
                                     (IF (SYMBOLP Y) (NOT (SYMBOL-< Y X)) 'T)
                                     (IF (SYMBOLP Y)
                                         'NIL
                                         (BAD-ATOM<= X Y))))))))))))

(DEFUN LEXORDER (X Y)
       (IF (ATOM X)
           (IF (ATOM Y) (ALPHORDER X Y) 'T)
           (IF (ATOM Y)
               'NIL
               (IF (EQUAL (CAR X) (CAR Y))
                   (LEXORDER (CDR X) (CDR Y))
                   (LEXORDER (CAR X) (CAR Y))))))

(DEFTHM ALPHORDER-REFLEXIVE (IMPLIES (NOT (CONSP X)) (ALPHORDER X X)))

(DEFTHM ALPHORDER-TRANSITIVE
        (IMPLIES (IF (ALPHORDER X Y)
                     (IF (ALPHORDER Y Z)
                         (IF (NOT (CONSP X))
                             (IF (NOT (CONSP Y))
                                 (NOT (CONSP Z))
                                 'NIL)
                             'NIL)
                         'NIL)
                     'NIL)
                 (ALPHORDER X Z)))

(DEFTHM ALPHORDER-ANTI-SYMMETRIC
        (IMPLIES (IF (NOT (CONSP X))
                     (IF (NOT (CONSP Y))
                         (IF (ALPHORDER X Y)
                             (ALPHORDER Y X)
                             'NIL)
                         'NIL)
                     'NIL)
                 (EQUAL X Y)))

(DEFTHM ALPHORDER-TOTAL
        (IMPLIES (IF (NOT (CONSP X))
                     (NOT (CONSP Y))
                     'NIL)
                 (IF (ALPHORDER X Y)
                     (ALPHORDER X Y)
                     (ALPHORDER Y X))))

(DEFTHM LEXORDER-REFLEXIVE (LEXORDER X X))

(DEFTHM LEXORDER-ANTI-SYMMETRIC
        (IMPLIES (IF (LEXORDER X Y) (LEXORDER Y X) 'NIL)
                 (EQUAL X Y)))

(DEFTHM LEXORDER-TRANSITIVE
        (IMPLIES (IF (LEXORDER X Y) (LEXORDER Y Z) 'NIL)
                 (LEXORDER X Z)))

(DEFTHM LEXORDER-TOTAL (IF (LEXORDER X Y) (LEXORDER X Y) (LEXORDER Y X)))

(DEFUN MERGE-LEXORDER (L1 L2 ACC)
       (IF (ENDP L1)
           (REVAPPEND ACC L2)
           (IF (ENDP L2)
               (REVAPPEND ACC L1)
               (IF (LEXORDER (CAR L1) (CAR L2))
                   (MERGE-LEXORDER (CDR L1)
                                   L2 (CONS (CAR L1) ACC))
                   (MERGE-LEXORDER L1 (CDR L2)
                                   (CONS (CAR L2) ACC))))))

(DEFTHM TRUE-LISTP-MERGE-SORT-LEXORDER
        (IMPLIES (IF (TRUE-LISTP L1)
                     (TRUE-LISTP L2)
                     'NIL)
                 (TRUE-LISTP (MERGE-LEXORDER L1 L2 ACC))))

(DEFUN MERGE-SORT-LEXORDER (L)
       (IF (ENDP (CDR L))
           L
           (MERGE-LEXORDER (MERGE-SORT-LEXORDER (EVENS L))
                           (MERGE-SORT-LEXORDER (ODDS L))
                           'NIL)))

(DEFUN IF* (X Y Z) (IF X Y Z))

(DEFUN RESIZE-LIST (LST N DEFAULT-VALUE)
       (IF (IF (INTEGERP N) (< '0 N) 'NIL)
           (CONS (IF (ATOM LST) DEFAULT-VALUE (CAR LST))
                 (RESIZE-LIST (IF (ATOM LST) LST (CDR LST))
                              (BINARY-+ '-1 N)
                              DEFAULT-VALUE))
           'NIL))

(DEFUN
   E/D-FN (THEORY E/D-LIST ENABLE-P)
   (IF (ATOM E/D-LIST)
       THEORY
       (IF ENABLE-P
           (E/D-FN (CONS 'UNION-THEORIES
                         (CONS THEORY
                               (CONS (CONS 'QUOTE (CONS (CAR E/D-LIST) 'NIL))
                                     'NIL)))
                   (CDR E/D-LIST)
                   'NIL)
           (E/D-FN (CONS 'SET-DIFFERENCE-THEORIES
                         (CONS THEORY
                               (CONS (CONS 'QUOTE (CONS (CAR E/D-LIST) 'NIL))
                                     'NIL)))
                   (CDR E/D-LIST)
                   'T))))

(DEFUN MOD-EXPT (BASE EXP MOD) (MOD (EXPT BASE EXP) MOD))

(DEFUN CONJOIN2 (T1 T2)
       (IF (EQUAL T1 ''NIL)
           ''NIL
           (IF (EQUAL T2 ''NIL)
               ''NIL
               (IF (EQUAL T1 ''T)
                   T2
                   (IF (EQUAL T2 ''T)
                       T1
                       (CONS 'IF
                             (CONS T1 (CONS T2 (CONS ''NIL 'NIL)))))))))

(DEFUN CONJOIN (L)
       (IF (ENDP L)
           ''T
           (IF (ENDP (CDR L))
               (CAR L)
               (CONJOIN2 (CAR L) (CONJOIN (CDR L))))))

(DEFUN DISJOIN2 (T1 T2)
       (IF (EQUAL T1 ''T)
           ''T
           (IF (EQUAL T2 ''T)
               ''T
               (IF (EQUAL T1 ''NIL)
                   T2
                   (IF (EQUAL T2 ''NIL)
                       T1
                       (CONS 'IF
                             (CONS T1 (CONS ''T (CONS T2 'NIL)))))))))

(DEFUN DISJOIN (LST)
       (IF (ENDP LST)
           ''NIL
           (IF (ENDP (CDR LST))
               (CAR LST)
               (DISJOIN2 (CAR LST)
                         (DISJOIN (CDR LST))))))

(DEFUN DISJOIN-LST (CLAUSE-LIST)
       (IF (ENDP CLAUSE-LIST)
           'NIL
           (CONS (DISJOIN (CAR CLAUSE-LIST))
                 (DISJOIN-LST (CDR CLAUSE-LIST)))))

(DEFUN CONJOIN-CLAUSES (CLAUSE-LIST) (CONJOIN (DISJOIN-LST CLAUSE-LIST)))

(DEFUN CLAUSES-RESULT (TUPLE)
       (IF (CAR TUPLE)
           (CONS 'NIL 'NIL)
           (CAR (CDR TUPLE))))

(DEFUN
    SPLICE-KEYWORD-ALIST
    (KEY NEW-SEGMENT KEYWORD-ALIST)
    (IF (ENDP KEYWORD-ALIST)
        'NIL
        (IF (EQ KEY (CAR KEYWORD-ALIST))
            (BINARY-APPEND NEW-SEGMENT (CDR (CDR KEYWORD-ALIST)))
            (CONS (CAR KEYWORD-ALIST)
                  (CONS (CAR (CDR KEYWORD-ALIST))
                        (SPLICE-KEYWORD-ALIST KEY NEW-SEGMENT
                                              (CDR (CDR KEYWORD-ALIST))))))))

(DEFUN
 SEARCH-FN-GUARD
 (SEQ1 SEQ2 FROM-END TEST
       START1 START2 END1 END2 END1P END2P)
 (IF
  (IF
   (NOT (MEMBER-EQ TEST '(EQUAL CHAR-EQUAL)))
   (HARD-ERROR
    'SEARCH
    '"For the macro ~x0, only the :test values ~x1 and ~x2 are ~
                   supported; ~x3 is not.  If you need other tests supported, ~
                   please contact the ACL2 implementors."
    (CONS (CONS '#\0 'SEARCH)
          (CONS (CONS '#\1 'EQUAL)
                (CONS (CONS '#\2 'CHAR-EQUAL)
                      (CONS (CONS '#\3 TEST) 'NIL)))))
   (IF
    (IF (STRINGP SEQ1) (STRINGP SEQ2) 'NIL)
    (IF
     (IF (STANDARD-CHAR-LISTP (COERCE SEQ1 'LIST))
         (STANDARD-CHAR-LISTP (COERCE SEQ2 'LIST))
         'NIL)
     (IF (STANDARD-CHAR-LISTP (COERCE SEQ1 'LIST))
         (STANDARD-CHAR-LISTP (COERCE SEQ2 'LIST))
         'NIL)
     (HARD-ERROR
      'SEARCH
      '"When ~x0 is called on two strings, they must both ~
                       consist of standard characters.  However, this is not ~
                       the case for ~x1."
      (CONS (CONS '#\0 'SEARCH)
            (CONS (CONS '#\1
                        (IF (STANDARD-CHAR-LISTP (COERCE SEQ1 'LIST))
                            SEQ2 SEQ1))
                  'NIL))))
    (IF
     (EQ TEST 'CHAR-EQUAL)
     (HARD-ERROR
      'SEARCH
      '"For the macro ~x0, the :test ~x1 is only supported for ~
                   string arguments.  If you need this test supported for ~
                   true lists, please contact the ACL2 implementors."
      (CONS (CONS '#\0 'SEARCH)
            (CONS (CONS '#\1 'CHAR-EQUAL) 'NIL)))
     (IF
      (IF (TRUE-LISTP SEQ1)
          (TRUE-LISTP SEQ2)
          'NIL)
      'T
      (HARD-ERROR
       'SEARCH
       '"The first two arguments of ~x0 much both evaluate to true ~
                   lists or must both evaluate to strings."
       (CONS (CONS '#\0 'SEARCH) 'NIL))))))
  ((LAMBDA (END1 END2 SEQ2 SEQ1 START2 START1)
           (IF (NATP START1)
               (IF (NATP START2)
                   (IF (NATP END1)
                       (IF (NATP END2)
                           (IF (NOT (< END1 START1))
                               (IF (NOT (< END2 START2))
                                   (IF (NOT (< (LENGTH SEQ1) END1))
                                       (NOT (< (LENGTH SEQ2) END2))
                                       'NIL)
                                   'NIL)
                               'NIL)
                           'NIL)
                       'NIL)
                   'NIL)
               'NIL))
   (IF END1P END1 (LENGTH SEQ1))
   (IF END2P END2 (LENGTH SEQ2))
   SEQ2 SEQ1 START2 START1)
  'NIL))

(DEFUN SEARCH-FROM-START
       (SEQ1 SEQ2 START2 END2)
       ((LAMBDA (BOUND2 SEQ2 SEQ1 START2 END2)
                (IF (IF (NOT (INTEGERP END2))
                        (NOT (INTEGERP END2))
                        (NOT (INTEGERP START2)))
                    'NIL
                    (IF (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                        START2
                        (IF (NOT (< BOUND2 END2))
                            'NIL
                            (SEARCH-FROM-START SEQ1 SEQ2 (BINARY-+ '1 START2)
                                               END2)))))
        (BINARY-+ START2 (LENGTH SEQ1))
        SEQ2 SEQ1 START2 END2))

(DEFUN
 SEARCH-FROM-END
 (SEQ1 SEQ2 START2 END2 ACC)
 (IF
  (IF (NOT (INTEGERP END2))
      (NOT (INTEGERP END2))
      (NOT (INTEGERP START2)))
  'NIL
  ((LAMBDA
        (BOUND2 ACC END2 START2 SEQ2 SEQ1)
        ((LAMBDA (MATCHP BOUND2 END2 SEQ1 SEQ2 ACC START2)
                 ((LAMBDA (NEW-ACC START2 SEQ2 SEQ1 END2 BOUND2)
                          (IF (NOT (< BOUND2 END2))
                              NEW-ACC
                              (SEARCH-FROM-END SEQ1 SEQ2 (BINARY-+ '1 START2)
                                               END2 NEW-ACC)))
                  (IF MATCHP START2 ACC)
                  START2 SEQ2 SEQ1 END2 BOUND2))
         (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
         BOUND2 END2 SEQ1 SEQ2 ACC START2))
   (BINARY-+ START2 (LENGTH SEQ1))
   ACC END2 START2 SEQ2 SEQ1)))

(DEFUN
 SEARCH-FN
 (SEQ1 SEQ2 FROM-END TEST
       START1 START2 END1 END2 END1P END2P)
 ((LAMBDA
   (END1 SEQ1 START1
         START2 FROM-END TEST SEQ2 END2 END2P)
   ((LAMBDA
     (END2 TEST
           SEQ2 FROM-END START2 END1 START1 SEQ1)
     ((LAMBDA
       (SEQ1 END2
             START2 END1 START1 FROM-END SEQ2 TEST)
       ((LAMBDA (MV FROM-END START1 END1 START2 END2)
                ((LAMBDA (SEQ1 SEQ2 FROM-END START1 END1 START2 END2)
                         (IF (NOT (< (BINARY-+ END2 (UNARY-- START2))
                                     (BINARY-+ END1 (UNARY-- START1))))
                             (IF FROM-END
                                 (SEARCH-FROM-END SEQ1 SEQ2 START2 END2 'NIL)
                                 (SEARCH-FROM-START SEQ1 SEQ2 START2 END2))
                             'NIL))
                 (MV-NTH '0 MV)
                 (MV-NTH '1 MV)
                 FROM-END START1 END1 START2 END2))
        (IF (EQ TEST 'CHAR-EQUAL)
            (CONS (STRING-DOWNCASE SEQ1)
                  (CONS (STRING-DOWNCASE SEQ2) 'NIL))
            (CONS SEQ1 (CONS SEQ2 'NIL)))
        FROM-END START1 END1 START2 END2))
      (SUBSEQ SEQ1 START1 END1)
      END2
      START2 END1 START1 FROM-END SEQ2 TEST))
    (IF END2P END2 (LENGTH SEQ2))
    TEST
    SEQ2 FROM-END START2 END1 START1 SEQ1))
  (IF END1P END1 (LENGTH SEQ1))
  SEQ1 START1
  START2 FROM-END TEST SEQ2 END2 END2P))
