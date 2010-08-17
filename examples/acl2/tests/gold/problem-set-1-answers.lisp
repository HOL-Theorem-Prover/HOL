(DEFPKG "M1"
        '(&REST * + - / < <= > >= ACL2-COUNT AND ASSOC
                ATOM CAR CASE CDR COERCE CONCATENATE
                COND CONS CONSP DECLARE DEFCONST
                DEFMACRO DEFTHM DEFUN DISABLE E/D ENDP
                EQUAL EXPT IF IGNORE IMPLIES IN-THEORY
                INCLUDE-BOOK INTERN-IN-PACKAGE-OF-SYMBOL
                LET LET* LIST
                LIST* MOD MUTUAL-RECURSION NATP NIL NOT
                O-P O< OR OTHERWISE PAIRLIS$ PAIRLIS-X2
                PROGN QUOTE QUOTEP STRING STRIP-CARS
                SYMBOL-NAME SYMBOLP SYNTAXP T XARGS ZP))

; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "M1")

(DEFUN M1::PUSH (M1::X M1::Y) (CONS M1::X M1::Y))

(DEFUN M1::TOP (M1::STACK) (CAR M1::STACK))

(DEFUN M1::POP (M1::STACK) (CDR M1::STACK))

(DEFUN M1::NTH (M1::N LIST)
       (IF (ZP M1::N)
           (CAR LIST)
           (M1::NTH (BINARY-+ '-1 M1::N)
                    (CDR LIST))))

(DEFUN M1::MAKE-STATE
       (M1::PC M1::LOCALS M1::STACK M1::PROGRAM)
       (CONS M1::PC
             (CONS M1::LOCALS
                   (CONS M1::STACK (CONS M1::PROGRAM 'NIL)))))

(DEFUN M1::PC (M1::S) (M1::NTH '0 M1::S))

(DEFUN M1::LOCALS (M1::S) (M1::NTH '1 M1::S))

(DEFUN M1::STACK (M1::S) (M1::NTH '2 M1::S))

(DEFUN M1::PROGRAM (M1::S) (M1::NTH '3 M1::S))

(DEFUN M1::OP-CODE (M1::INST) (CAR M1::INST))

(DEFUN M1::ARG1 (M1::INST) (M1::NTH '1 M1::INST))

(DEFUN M1::ARG2 (M1::INST) (M1::NTH '2 M1::INST))

(DEFUN M1::ARG3 (M1::INST) (M1::NTH '3 M1::INST))

(DEFUN M1::LEN (M1::X)
       (IF (ENDP M1::X)
           '0
           (BINARY-+ '1 (M1::LEN (CDR M1::X)))))

(DEFUN M1::APP (M1::X M1::Y)
       (IF (ENDP M1::X)
           M1::Y
           (CONS (CAR M1::X)
                 (M1::APP (CDR M1::X) M1::Y))))

(DEFUN M1::REV (M1::X)
       (IF (ENDP M1::X)
           'NIL
           (M1::APP (M1::REV (CDR M1::X))
                    (CONS (CAR M1::X) 'NIL))))

(DEFUN M1::REV1 (M1::X M1::A)
       (IF (ENDP M1::X)
           M1::A
           (M1::REV1 (CDR M1::X)
                     (CONS (CAR M1::X) M1::A))))

(DEFUN M1::FREV (M1::X) (M1::REV1 M1::X 'NIL))

(DEFUN M1::REPEAT (M1::TH M1::N)
       (IF (ZP M1::N)
           'NIL
           (CONS M1::TH
                 (M1::REPEAT M1::TH (BINARY-+ '-1 M1::N)))))

(DEFUN M1::POPN (M1::N M1::STK)
       (IF (ZP M1::N)
           M1::STK
           (M1::POPN (BINARY-+ '-1 M1::N)
                     (M1::POP M1::STK))))

(DEFUN M1::UPDATE-NTH (M1::N M1::V LIST)
       (IF (ZP M1::N)
           (CONS M1::V (CDR LIST))
           (CONS (CAR LIST)
                 (M1::UPDATE-NTH (BINARY-+ '-1 M1::N)
                                 M1::V (CDR LIST)))))

(DEFUN M1::MEMBER (M1::E LIST)
       (IF (ENDP LIST)
           'NIL
           (IF (EQUAL M1::E (CAR LIST))
               'T
               (M1::MEMBER M1::E (CDR LIST)))))

(DEFUN M1::INDEX (M1::E M1::LST)
       (IF (ENDP M1::LST)
           '0
           (IF (EQUAL M1::E (CAR M1::LST))
               '0
               (BINARY-+ '1
                         (M1::INDEX M1::E (CDR M1::LST))))))

(DEFUN M1::SUPPLIEDP (M1::KEY M1::ARGS)
       (IF (ENDP M1::ARGS)
           'NIL
           (IF (EQUAL M1::KEY (CAR M1::ARGS))
               'T
               (M1::SUPPLIEDP M1::KEY (CDR (CDR M1::ARGS))))))

(DEFUN M1::ACTUAL (M1::KEY M1::ARGS)
       (IF (ENDP M1::ARGS)
           'NIL
           (IF (EQUAL M1::KEY (CAR M1::ARGS))
               (CAR (CDR M1::ARGS))
               (M1::ACTUAL M1::KEY (CDR (CDR M1::ARGS))))))

(DEFUN M1::BOUNDP (M1::VAR M1::ALIST)
       (IF (ENDP M1::ALIST)
           'NIL
           (IF (EQUAL M1::VAR (CAR (CAR M1::ALIST)))
               'T
               (M1::BOUNDP M1::VAR (CDR M1::ALIST)))))

(DEFUN M1::BINDING (M1::VAR M1::ALIST)
       (IF (ENDP M1::ALIST)
           'NIL
           (IF (EQUAL M1::VAR (CAR (CAR M1::ALIST)))
               (CAR (CDR (CAR M1::ALIST)))
               (M1::BINDING M1::VAR (CDR M1::ALIST)))))

(DEFUN M1::BIND (M1::VAR M1::VAL M1::ALIST)
       (IF (ENDP M1::ALIST)
           (CONS (CONS M1::VAR (CONS M1::VAL 'NIL))
                 'NIL)
           (IF (EQUAL M1::VAR (CAR (CAR M1::ALIST)))
               (CONS (CONS M1::VAR (CONS M1::VAL 'NIL))
                     (CDR M1::ALIST))
               (CONS (CAR M1::ALIST)
                     (M1::BIND M1::VAR M1::VAL (CDR M1::ALIST))))))

(DEFUN M1::U-FIX (M1::X M1::N) (MOD M1::X (EXPT '2 M1::N)))

(DEFUN M1::S-FIX (M1::X M1::N)
       ((LAMBDA (M1::TEMP M1::N)
                (IF (< M1::TEMP (EXPT '2 (BINARY-+ '-1 M1::N)))
                    M1::TEMP
                    (BINARY-+ M1::TEMP (UNARY-- (EXPT '2 M1::N)))))
        (MOD M1::X (EXPT '2 M1::N))
        M1::N))

(DEFUN M1::U-BIG1 (M1::LST M1::ACC)
       (IF (ENDP M1::LST)
           M1::ACC
           (M1::U-BIG1 (CDR M1::LST)
                       (BINARY-+ (M1::U-FIX (CAR M1::LST) '8)
                                 (BINARY-* (EXPT '2 '8) M1::ACC)))))

(DEFUN M1::U-BIG (M1::LST) (M1::U-BIG1 M1::LST '0))

(DEFUN M1::S-BIG (M1::LST)
       (M1::S-FIX (M1::U-BIG M1::LST)
                  (BINARY-* '8 (M1::LEN M1::LST))))

(DEFUN M1::NEXTN (M1::N M1::LST)
       (IF (ZP M1::N)
           'NIL
           (CONS (CAR M1::LST)
                 (M1::NEXTN (BINARY-+ '-1 M1::N)
                            (CDR M1::LST)))))

(DEFUN M1::SKIPN (M1::N M1::LST)
       (IF (ZP M1::N)
           M1::LST
           (M1::SKIPN (BINARY-+ '-1 M1::N)
                      (CDR M1::LST))))
