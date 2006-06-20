val name_alist =
map (fn s => (acl2_name_to_hol_name s, s))
[
"ACL2::IFF",
"ACL2::BOOLEANP",
"ACL2::IMPLIES",
"COMMON-LISP::NOT",
"ACL2::HIDE",
"COMMON-LISP::EQ",
"ACL2::TRUE-LISTP",
"ACL2::LIST-MACRO",
"ACL2::AND-MACRO",
"ACL2::OR-MACRO",
"ACL2::INTEGER-ABS",
"ACL2::XXXJOIN",
"ACL2::LEN",
"COMMON-LISP::LENGTH",
"ACL2::ACL2-COUNT",
"ACL2::COND-CLAUSESP",
"ACL2::COND-MACRO",
"ACL2::EQLABLEP",
"ACL2::EQLABLE-LISTP",
"COMMON-LISP::ATOM",
"ACL2::MAKE-CHARACTER-LIST",
"ACL2::EQLABLE-ALISTP",
"ACL2::ALISTP",
"COMMON-LISP::ACONS",
"COMMON-LISP::ENDP",
"ACL2::MUST-BE-EQUAL",
"ACL2::MEMBER-EQUAL",
"ACL2::UNION-EQUAL",
"ACL2::SUBSETP-EQUAL",
"ACL2::SYMBOL-LISTP",
"COMMON-LISP::NULL",
"ACL2::MEMBER-EQ",
"ACL2::SUBSETP-EQ",
"ACL2::SYMBOL-ALISTP",
"ACL2::ASSOC-EQ",
"ACL2::ASSOC-EQUAL",
"ACL2::ASSOC-EQ-EQUAL-ALISTP",
"ACL2::ASSOC-EQ-EQUAL",
"ACL2::NO-DUPLICATESP-EQUAL",
"ACL2::STRIP-CARS",
"COMMON-LISP::EQL",
"COMMON-LISP::=",
"COMMON-LISP::/=",
"ACL2::ZP",
"ACL2::ZIP",
"COMMON-LISP::NTH",
"COMMON-LISP::CHAR",
"ACL2::PROPER-CONSP",
"ACL2::IMPROPER-CONSP",
"COMMON-LISP::CONJUGATE",
"ACL2::PROG2$",
"ACL2::TIME$",
"ACL2::FIX",
"ACL2::FORCE",
"ACL2::IMMEDIATE-FORCE-MODEP",
"ACL2::CASE-SPLIT",
"ACL2::SYNP",
"COMMON-LISP::MEMBER",
"ACL2::NO-DUPLICATESP",
"COMMON-LISP::ASSOC",
"ACL2::R-EQLABLE-ALISTP",
"COMMON-LISP::RASSOC",
"ACL2::RASSOC-EQUAL",
"ACL2::R-SYMBOL-ALISTP",
"ACL2::RASSOC-EQ"];

val defuns =
[
`(DEFUN IFF (P Q)
       (IF P (IF Q 'T 'NIL) (IF Q 'NIL 'T)))`,


`(DEFUN BOOLEANP (X)
       (IF (EQUAL X 'T) 'T (EQUAL X 'NIL)))`,


`(DEFUN IMPLIES (P Q)
       (IF P (IF Q 'T 'NIL) 'T))`,


`(DEFUN NOT (P) (IF P 'NIL 'T))`,


`(DEFUN HIDE (X) X)`,


`(DEFUN EQ (X Y) (EQUAL X Y))`,


`(DEFUN TRUE-LISTP (X)
       (IF (CONSP X)
           (TRUE-LISTP (CDR X))
           (EQ X 'NIL)))`,


`(DEFUN LIST-MACRO (LST)
       (IF (CONSP LST)
           (CONS 'CONS
                 (CONS (CAR LST)
                       (CONS (LIST-MACRO (CDR LST)) 'NIL)))
           'NIL))`,


`(DEFUN AND-MACRO (LST)
       (IF (CONSP LST)
           (IF (CONSP (CDR LST))
               (CONS 'IF
                     (CONS (CAR LST)
                           (CONS (AND-MACRO (CDR LST))
                                 (CONS 'NIL 'NIL))))
               (CAR LST))
           'T))`,


`(DEFUN OR-MACRO (LST)
       (IF (CONSP LST)
           (IF (CONSP (CDR LST))
               (CONS 'IF
                     (CONS (CAR LST)
                           (CONS (CAR LST)
                                 (CONS (OR-MACRO (CDR LST)) 'NIL))))
               (CAR LST))
           'NIL))`,


`(DEFUN INTEGER-ABS (X)
       (IF (INTEGERP X)
           (IF (< X '0) (UNARY-- X) X)
           '0))`,


`(DEFUN XXXJOIN (FN ARGS)
       (IF (CDR (CDR ARGS))
           (CONS FN
                 (CONS (CAR ARGS)
                       (CONS (XXXJOIN FN (CDR ARGS)) 'NIL)))
           (CONS FN ARGS)))`,


`(DEFUN LEN (X)
       (IF (CONSP X)
           (BINARY-+ '1 (LEN (CDR X)))
           '0))`,


`(DEFUN LENGTH (X)
       (IF (STRINGP X)
           (LEN (COERCE X 'LIST))
           (LEN X)))`,


`(DEFUN ACL2-COUNT (X)
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
                   (IF (STRINGP X) (LENGTH X) '0)))))`,


`(DEFUN COND-CLAUSESP (CLAUSES)
       (IF (CONSP CLAUSES)
           (IF (CONSP (CAR CLAUSES))
               (IF (TRUE-LISTP (CAR CLAUSES))
                   (IF (< (LEN (CAR CLAUSES)) '3)
                       (IF (EQ (CAR (CAR CLAUSES)) 'T)
                           (EQ (CDR CLAUSES) 'NIL)
                           (COND-CLAUSESP (CDR CLAUSES)))
                       'NIL)
                   'NIL)
               'NIL)
           (EQ CLAUSES 'NIL)))`,


`(DEFUN COND-MACRO (CLAUSES)
       (IF (CONSP CLAUSES)
           (IF (EQ (CAR (CAR CLAUSES)) 'T)
               (IF (CDR (CAR CLAUSES))
                   (CAR (CDR (CAR CLAUSES)))
                   (CAR (CAR CLAUSES)))
               (CONS 'IF
                     (CONS (CAR (CAR CLAUSES))
                           (CONS (IF (CDR (CAR CLAUSES))
                                     (CAR (CDR (CAR CLAUSES)))
                                     (CAR (CAR CLAUSES)))
                                 (CONS (COND-MACRO (CDR CLAUSES))
                                       'NIL)))))
           'NIL))`,


`(DEFUN EQLABLEP (X)
       (IF (ACL2-NUMBERP X)
           (ACL2-NUMBERP X)
           (IF (SYMBOLP X)
               (SYMBOLP X)
               (CHARACTERP X))))`,


`(DEFUN EQLABLE-LISTP (L)
       (IF (CONSP L)
           (IF (EQLABLEP (CAR L))
               (EQLABLE-LISTP (CDR L))
               'NIL)
           (EQUAL L 'NIL)))`,


`(DEFUN ATOM (X) (NOT (CONSP X)))`,


`(DEFUN MAKE-CHARACTER-LIST (X)
       (IF (ATOM X)
           'NIL
           (IF (CHARACTERP (CAR X))
               (CONS (CAR X)
                     (MAKE-CHARACTER-LIST (CDR X)))
               (CONS (CODE-CHAR '0)
                     (MAKE-CHARACTER-LIST (CDR X))))))`,


`(DEFUN EQLABLE-ALISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (CONSP (CAR X))
               (IF (EQLABLEP (CAR (CAR X)))
                   (EQLABLE-ALISTP (CDR X))
                   'NIL)
               'NIL)))`,


`(DEFUN ALISTP (L)
       (IF (ATOM L)
           (EQ L 'NIL)
           (IF (CONSP (CAR L))
               (ALISTP (CDR L))
               'NIL)))`,


`(DEFUN ACONS (KEY DATUM ALIST)
       (CONS (CONS KEY DATUM) ALIST))`,


`(DEFUN ENDP (X) (ATOM X))`,


`(DEFUN MUST-BE-EQUAL (LOGIC EXEC) LOGIC)`,


`(DEFUN MEMBER-EQUAL (X LST)
       (IF (ENDP LST)
           'NIL
           (IF (EQUAL X (CAR LST))
               LST (MEMBER-EQUAL X (CDR LST)))))`,


`(DEFUN UNION-EQUAL (X Y)
       (IF (ENDP X)
           Y
           (IF (MEMBER-EQUAL (CAR X) Y)
               (UNION-EQUAL (CDR X) Y)
               (CONS (CAR X)
                     (UNION-EQUAL (CDR X) Y)))))`,


`(DEFUN SUBSETP-EQUAL (X Y)
       (IF (ENDP X)
           'T
           (IF (MEMBER-EQUAL (CAR X) Y)
               (SUBSETP-EQUAL (CDR X) Y)
               'NIL)))`,


`(DEFUN SYMBOL-LISTP (LST)
       (IF (ATOM LST)
           (EQ LST 'NIL)
           (IF (SYMBOLP (CAR LST))
               (SYMBOL-LISTP (CDR LST))
               'NIL)))`,


`(DEFUN NULL (X) (EQ X 'NIL))`,


`(DEFUN MEMBER-EQ (X LST)
       (IF (ENDP LST)
           'NIL
           (IF (EQ X (CAR LST))
               LST (MEMBER-EQ X (CDR LST)))))`,


`(DEFUN SUBSETP-EQ (X Y)
       (IF (ENDP X)
           'T
           (IF (MEMBER-EQ (CAR X) Y)
               (SUBSETP-EQ (CDR X) Y)
               'NIL)))`,


`(DEFUN SYMBOL-ALISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (CONSP (CAR X))
               (IF (SYMBOLP (CAR (CAR X)))
                   (SYMBOL-ALISTP (CDR X))
                   'NIL)
               'NIL)))`,


`(DEFUN ASSOC-EQ (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQ X (CAR (CAR ALIST)))
               (CAR ALIST)
               (ASSOC-EQ X (CDR ALIST)))))`,


`(DEFUN ASSOC-EQUAL (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQUAL X (CAR (CAR ALIST)))
               (CAR ALIST)
               (ASSOC-EQUAL X (CDR ALIST)))))`,


`(DEFUN ASSOC-EQ-EQUAL-ALISTP (X)
       (IF (ATOM X)
           (EQ X 'NIL)
           (IF (CONSP (CAR X))
               (IF (SYMBOLP (CAR (CAR X)))
                   (IF (CONSP (CDR (CAR X)))
                       (ASSOC-EQ-EQUAL-ALISTP (CDR X))
                       'NIL)
                   'NIL)
               'NIL)))`,


`(DEFUN ASSOC-EQ-EQUAL (X Y ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (IF (EQ (CAR (CAR ALIST)) X)
                   (EQUAL (CAR (CDR (CAR ALIST))) Y)
                   'NIL)
               (CAR ALIST)
               (ASSOC-EQ-EQUAL X Y (CDR ALIST)))))`,


`(DEFUN NO-DUPLICATESP-EQUAL (L)
       (IF (ENDP L)
           'T
           (IF (MEMBER-EQUAL (CAR L) (CDR L))
               'NIL
               (NO-DUPLICATESP-EQUAL (CDR L)))))`,


`(DEFUN STRIP-CARS (X)
       (IF (ENDP X)
           'NIL
           (CONS (CAR (CAR X))
                 (STRIP-CARS (CDR X)))))`,


`(DEFUN EQL (X Y) (EQUAL X Y))`,


`(DEFUN = (X Y) (EQUAL X Y))`,


`(DEFUN /= (X Y) (NOT (EQUAL X Y)))`,


`(DEFUN ZP (X)
       (IF (INTEGERP X) (NOT (< '0 X)) 'T))`,


`(DEFUN ZIP (X)
       (IF (INTEGERP X) (= X '0) 'T))`,


`(DEFUN NTH (N L)
       (IF (ENDP L)
           'NIL
           (IF (ZP N)
               (CAR L)
               (NTH (BINARY-+ '-1 N) (CDR L)))))`,


`(DEFUN CHAR (S N)
       (NTH N (COERCE S 'LIST)))`,


`(DEFUN PROPER-CONSP (X)
       (IF (CONSP X) (TRUE-LISTP X) 'NIL))`,


`(DEFUN IMPROPER-CONSP (X)
       (IF (CONSP X)
           (NOT (TRUE-LISTP X))
           'NIL))`,


`(DEFUN CONJUGATE (X)
       (IF (COMPLEX-RATIONALP X)
           (COMPLEX (REALPART X)
                    (UNARY-- (IMAGPART X)))
           X))`,


`(DEFUN PROG2$ (X Y) Y)`,


`(DEFUN TIME$ (X) X)`,


`(DEFUN FIX (X)
       (IF (ACL2-NUMBERP X) X '0))`,


`(DEFUN FORCE (X) X)`,


`(DEFUN IMMEDIATE-FORCE-MODEP
       NIL '"See :DOC immediate-force-modep.")`,


`(DEFUN CASE-SPLIT (X) X)`,


`(DEFUN SYNP (VARS FORM TERM) 'T)`,


`(DEFUN MEMBER (X L)
       (IF (ENDP L)
           'NIL
           (IF (EQL X (CAR L))
               L (MEMBER X (CDR L)))))`,


`(DEFUN NO-DUPLICATESP (L)
       (IF (ENDP L)
           'T
           (IF (MEMBER (CAR L) (CDR L))
               'NIL
               (NO-DUPLICATESP (CDR L)))))`,


`(DEFUN ASSOC (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQL X (CAR (CAR ALIST)))
               (CAR ALIST)
               (ASSOC X (CDR ALIST)))))`,


`(DEFUN R-EQLABLE-ALISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (CONSP (CAR X))
               (IF (EQLABLEP (CDR (CAR X)))
                   (R-EQLABLE-ALISTP (CDR X))
                   'NIL)
               'NIL)))`,


`(DEFUN RASSOC (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQL X (CDR (CAR ALIST)))
               (CAR ALIST)
               (RASSOC X (CDR ALIST)))))`,


`(DEFUN RASSOC-EQUAL (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQUAL X (CDR (CAR ALIST)))
               (CAR ALIST)
               (RASSOC-EQUAL X (CDR ALIST)))))`,


`(DEFUN R-SYMBOL-ALISTP (X)
       (IF (ATOM X)
           (EQUAL X 'NIL)
           (IF (CONSP (CAR X))
               (IF (SYMBOLP (CDR (CAR X)))
                   (R-SYMBOL-ALISTP (CDR X))
                   'NIL)
               'NIL)))`,           


`(DEFUN RASSOC-EQ (X ALIST)
       (IF (ENDP ALIST)
           'NIL
           (IF (EQ X (CDR (CAR ALIST)))
               (CAR ALIST)
               (RASSOC-EQ X (CDR ALIST)))))`
];
