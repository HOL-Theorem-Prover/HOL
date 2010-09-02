(DEFPKG "MY-PKG" '(CONS DEFUN))

; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "MY-PKG")

(DEFUN MY-PKG::F1 (MY-PKG::X) (CONS MY-PKG::X MY-PKG::X))

(DEFUN MY-PKG::F2 (MY-PKG::X) (BINARY-APPEND MY-PKG::X MY-PKG::X))

(DEFUN MY-PKG::CONSTS NIL '(MY-PKG::X DEFUN CONS))

(DEFTHM
     TEST0
     ((LAMBDA (LST)
              (IF (EQUAL (CAR LST) 'MY-PKG::X)
                  (IF (NOT (EQUAL (CAR LST) 'X))
                      (IF (EQUAL (CAR (CDR LST)) 'DEFUN)
                          (IF (EQUAL (CAR (CDR LST)) 'DEFUN)
                              (IF (EQUAL (CAR (CDR LST)) 'DEFUN)
                                  (IF (EQUAL (CAR (CDR (CDR LST))) 'CONS)
                                      (IF (EQUAL (CAR (CDR (CDR LST))) 'CONS)
                                          (EQUAL (CAR (CDR (CDR LST))) 'CONS)
                                          'NIL)
                                      'NIL)
                                  'NIL)
                              'NIL)
                          'NIL)
                      'NIL)
                  'NIL))
      (MY-PKG::CONSTS)))

(DEFTHM TEST1A (EQUAL (SYMBOL-PACKAGE-NAME 'MY-PKG::C) '"MY-PKG"))

(DEFTHM TEST1B (EQUAL (SYMBOL-NAME 'MY-PKG::C) '"C"))

(DEFTHM TEST2A (EQUAL (SYMBOL-PACKAGE-NAME 'DEFUN) '"COMMON-LISP"))

(DEFTHM TEST2B (EQUAL (SYMBOL-NAME 'DEFUN) '"DEFUN"))

(DEFTHM TEST3A (EQUAL (SYMBOL-PACKAGE-NAME 'MY-PKG::|defun|) '"MY-PKG"))

(DEFTHM TEST3B (EQUAL (SYMBOL-NAME 'MY-PKG::|defun|) '"defun"))

(DEFTHM TEST4
        (EQUAL (INTERN-IN-PACKAGE-OF-SYMBOL '"DEFUN"
                                            'MY-PKG::C)
               (INTERN-IN-PACKAGE-OF-SYMBOL '"DEFUN"
                                            'COMMON-LISP::C)))

(DEFTHM TEST5
        (NOT (EQUAL (INTERN-IN-PACKAGE-OF-SYMBOL '"defun"
                                                 'MY-PKG::C)
                    (INTERN-IN-PACKAGE-OF-SYMBOL '"defun"
                                                 'COMMON-LISP::C))))

(DEFTHM TEST6
        (NOT (EQUAL (INTERN-IN-PACKAGE-OF-SYMBOL '"D"
                                                 'MY-PKG::C)
                    (INTERN-IN-PACKAGE-OF-SYMBOL '"D"
                                                 'COMMON-LISP::C))))
