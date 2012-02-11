;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; core.lisp
;  - used by Common Lisp systems and also Jitawa
;  - contains core Milawa definitions

(define 'lookup-safe '(a x)
  '(if (consp x)
       (if (equal a (car (car x)))
           (if (consp (car x))
               (car x)
             (cons (car (car x)) (cdr (car x))))
         (lookup-safe a (cdr x)))
     'nil))

(define 'define-safe '(ftbl name formals body)
  ;; Returns FTBL-PRIME or causes an error.
  '(let* ((this-def (list name formals body))
          (prev-def (lookup-safe name ftbl)))
     (if prev-def
         (if (equal prev-def this-def)
             ftbl
           (error (list 'redefinition-error prev-def this-def)))
       (let ((unused (define name formals body)))
         (cons this-def ftbl)))))

(define 'define-safe-list '(ftbl defs)
  ;; DEFS are 3-tuples of the form: (name formals body)
  ;; We define all of these functions, in order.
  ;; We return FTBL-PRIME or causes an error.
  '(if (consp defs)
       (let* ((def1 (car defs))
              (ftbl (define-safe ftbl (first def1) (second def1) (third def1))))
         (define-safe-list ftbl (cdr defs)))
     ftbl))

(define 'milawa-init '()
  '(define-safe-list

; We start with "ill-formed" definitions for any functions we don't want the
; user to be able to redefine.  This list includes (1) all of the primitive
; Milawa functions like IF, EQUAL, etc., and (2) any built-in system functions
; that the Lisp relies upon.
;
; The point of this is to ensure that any attempt by the user to define any of
; these functions will fail.  No matter what formals and body they try to use,
; the resulting call of DEFUN-SAFE will insist that (F FORMALS BODY) is in the
; FTBL, but the actual entry is just (F).

     '(;; Milawa Primitives
       (if)
       (equal)
       (symbolp)
       (symbol-<)
       (natp)
       (<)
       (+)
       (-)
       (consp)
       (cons)
       (car)
       (cdr)

       ;; Extralogical System Functions
       (error)
       (print)
       (define)
       (defun)
       (funcall)
       (lookup-safe)
       (define-safe)
       (define-safe-list)
       (milawa-init)
       (milawa-main))

; We now extend the above FTBL wth definitions for all of the functions for our
; proof-checking system.  Note that the act of defining these functions does
; not "admit" them and add definitional axioms, but instead merely (1)
; introduces Lisp definitions of these functions and (2) installs FTBL entries
; for these functions so that the user may not define them in any other way.

     '((not (x) (if x nil t))

       (rank (x)
             (if (consp x)
                 (+ 1
                    (+ (rank (car x))
                       (rank (cdr x))))
               0))

       (ord< (x y)
             (cond ((not (consp x))
                    (if (consp y) t (< x y)))
                   ((not (consp y))
                    nil)
                   ((not (equal (car (car x)) (car (car y))))
                    (ord< (car (car x)) (car (car y))))
                   ((not (equal (cdr (car x)) (cdr (car y))))
                    (< (cdr (car x)) (cdr (car y))))
                   (t
                    (ord< (cdr x) (cdr y)))))

       (ordp (x)
             (if (not (consp x))
                 (natp x)
               (and (consp (car x))
                    (ordp (car (car x)))
                    (not (equal (car (car x)) 0))
                    (< 0 (cdr (car x)))
                    (ordp (cdr x))
                    (if (consp (cdr x))
                        (ord< (car (car (cdr x))) (car (car x)))
                      t))))

       (nfix (x) (if (natp x) x 0))

       (<= (a b) (not (< b a)))

       (zp (x) (if (natp x) (equal x 0) t))

       (true-listp (x)
                   (if (consp x)
                       (true-listp (cdr x))
                     (equal x nil)))

       (list-fix (x)
                 (if (consp x)
                     (cons (car x) (list-fix (cdr x)))
                   nil))

       (len (x)
            (if (consp x)
                (+ 1 (len (cdr x)))
              0))

       (memberp (a x)
                (if (consp x)
                    (or (equal a (car x))
                        (memberp a (cdr x)))
                  nil))

       (subsetp (x y)
                (if (consp x)
                    (and (memberp (car x) y)
                         (subsetp (cdr x) y))
                  t))

       (uniquep (x)
                (if (consp x)
                    (and (not (memberp (car x) (cdr x)))
                         (uniquep (cdr x)))
                  t))

       (app (x y)
            (if (consp x)
                (cons (car x) (app (cdr x) y))
              (list-fix y)))

       (rev (x)
            (if (consp x)
                (app (rev (cdr x)) (list (car x)))
              nil))

       (tuplep (n x)
               (if (zp n)
                   (equal x nil)
                 (and (consp x)
                      (tuplep (- n 1) (cdr x)))))

       (pair-lists (x y)
                   (if (consp x)
                       (cons (cons (car x) (car y))
                             (pair-lists (cdr x) (cdr y)))
                     nil))

       (lookup (a x)
               (if (consp x)
                   (if (equal a (car (car x)))
                       (if (consp (car x))
                           (car x)
                         (cons (car (car x)) (cdr (car x))))
                     (lookup a (cdr x)))
                 nil))

       ;; THE PROOF CHECKER - TERMS

       (|LOGIC.VARIABLEP| (x)
        (and (symbolp x)
             (not (equal x t))
             (not (equal x nil))))

       (|LOGIC.VARIABLE-LISTP| (x)
        (if (consp x)
            (and (|LOGIC.VARIABLEP| (car x))
                 (|LOGIC.VARIABLE-LISTP| (cdr x)))
          t))

       (|LOGIC.CONSTANTP| (x)
        (and (tuplep 2 x)
             (equal (first x) 'quote)))

       (|LOGIC.CONSTANT-LISTP| (x)
        (if (consp x)
            (and (|LOGIC.CONSTANTP| (car x))
                 (|LOGIC.CONSTANT-LISTP| (cdr x)))
          t))

       (|LOGIC.FUNCTION-NAMEP| (x)
        (and (symbolp x)
             (not (memberp x '(nil quote pequal* pnot*
                                   por* first second third
                                   fourth fifth and or list
                                   cond let let*)))))

       (|LOGIC.FLAG-TERM-VARS| (flag x acc)
        (if (equal flag 'term)
            (cond ((|LOGIC.CONSTANTP| x) acc)
                  ((|LOGIC.VARIABLEP| x) (cons x acc))
                  ((not (consp x))     acc)
                  (t
                   (|LOGIC.FLAG-TERM-VARS| 'list (cdr x) acc)))
          (if (consp x)
              (|LOGIC.FLAG-TERM-VARS| 'term (car x)
               (|LOGIC.FLAG-TERM-VARS| 'list (cdr x) acc))
            acc)))

       (|LOGIC.TERM-VARS| (x) (|LOGIC.FLAG-TERM-VARS| 'term x nil))

       (|LOGIC.FLAG-TERMP| (flag x)
        (if (equal flag 'term)
            (or (|LOGIC.VARIABLEP| x)
                (|LOGIC.CONSTANTP| x)
                (and (consp x)
                     (if (|LOGIC.FUNCTION-NAMEP| (car x))
                         (let ((args (cdr x)))
                           (and (true-listp args)
                                (|LOGIC.FLAG-TERMP| 'list args)))
                       (and (tuplep 3 (car x))
                            (let ((lambda-symbol (first (car x)))
                                  (formals       (second (car x)))
                                  (body          (third (car x)))
                                  (actuals       (cdr x)))
                              (and (equal lambda-symbol 'lambda)
                                   (true-listp formals)
                                   (|LOGIC.VARIABLE-LISTP| formals)
                                   (uniquep formals)
                                   (|LOGIC.FLAG-TERMP| 'term body)
                                   (subsetp (|LOGIC.TERM-VARS| body) formals)
                                   (equal (len formals) (len actuals))
                                   (true-listp actuals)
                                   (|LOGIC.FLAG-TERMP| 'list actuals)))))))
          (if (consp x)
              (and (|LOGIC.FLAG-TERMP| 'term (car x))
                   (|LOGIC.FLAG-TERMP| 'list (cdr x)))
            t)))

       (|LOGIC.TERMP| (x) (|LOGIC.FLAG-TERMP| 'term x))

       (|LOGIC.UNQUOTE| (x) (second x))

       (|LOGIC.UNQUOTE-LIST| (x)
        (if (consp x)
            (cons (|LOGIC.UNQUOTE| (car x))
                  (|LOGIC.UNQUOTE-LIST| (cdr x)))
          nil))

       (|LOGIC.FUNCTIONP| (x) (|LOGIC.FUNCTION-NAMEP| (car x)))
       (|LOGIC.FUNCTION-NAME| (x) (car x))
       (|LOGIC.FUNCTION-ARGS| (x) (cdr x))
       (|LOGIC.FUNCTION| (name args) (cons name args))

       (|LOGIC.LAMBDAP| (x) (consp (car x)))
       (|LOGIC.LAMBDA-FORMALS| (x) (second (car x)))
       (|LOGIC.LAMBDA-BODY|    (x) (third (car x)))
       (|LOGIC.LAMBDA-ACTUALS| (x) (cdr x))
       (|LOGIC.LAMBDA| (xs b ts) (cons (list 'lambda xs b) ts))

       (|LOGIC.FLAG-TERM-ATBLP| (flag x atbl)
        (if (equal flag 'term)
            (cond ((|LOGIC.CONSTANTP| x) t)
                  ((|LOGIC.VARIABLEP| x) t)
                  ((|LOGIC.FUNCTIONP| x)
                   (let ((name (|LOGIC.FUNCTION-NAME| x))
                         (args (|LOGIC.FUNCTION-ARGS| x)))
                     (and (equal (len args) (cdr (lookup name atbl)))
                          (|LOGIC.FLAG-TERM-ATBLP| 'list args atbl))))
                  ((|LOGIC.LAMBDAP| x)
                   (let ((body    (|LOGIC.LAMBDA-BODY| x))
                         (actuals (|LOGIC.LAMBDA-ACTUALS| x)))
                     (and (|LOGIC.FLAG-TERM-ATBLP| 'term body atbl)
                          (|LOGIC.FLAG-TERM-ATBLP| 'list actuals atbl))))
                  (t nil))
          (if (consp x)
              (and (|LOGIC.FLAG-TERM-ATBLP| 'term (car x) atbl)
                   (|LOGIC.FLAG-TERM-ATBLP| 'list (cdr x) atbl))
            t)))

       (|LOGIC.TERM-ATBLP| (x atbl)
        (|LOGIC.FLAG-TERM-ATBLP| 'term x atbl))


       ;; THE PROOF CHECKER - FORMULAS

       (|LOGIC.FORMULAP| (x)
        (cond ((equal (first x) 'pequal*)
               (and (tuplep 3 x)
                    (|LOGIC.TERMP| (second x))
                    (|LOGIC.TERMP| (third x))))
              ((equal (first x) 'pnot*)
               (and (tuplep 2 x)
                    (|LOGIC.FORMULAP| (second x))))
              ((equal (first x) 'por*)
               (and (tuplep 3 x)
                    (|LOGIC.FORMULAP| (second x))
                    (|LOGIC.FORMULAP| (third x))))
              (t nil)))

       (|LOGIC.FORMULA-LISTP| (x)
        (if (consp x)
            (and (|LOGIC.FORMULAP| (car x))
                 (|LOGIC.FORMULA-LISTP| (cdr x)))
          t))

       (|LOGIC.FMTYPE| (x) (first x))

       (|LOGIC.=LHS| (x) (second x))
       (|LOGIC.=RHS| (x) (third x))
       (|LOGIC.~ARG| (x) (second x))
       (|LOGIC.VLHS| (x) (second x))
       (|LOGIC.VRHS| (x) (third x))

       (|LOGIC.PEQUAL| (a b) (list 'pequal* a b))
       (|LOGIC.PNOT|   (a)   (list 'pnot* a))
       (|LOGIC.POR|    (a b) (list 'por* a b))

       (|LOGIC.FORMULA-ATBLP| (x atbl)
        (let ((type (|LOGIC.FMTYPE| x)))
          (cond ((equal type 'por*)
                 (and (|LOGIC.FORMULA-ATBLP| (|LOGIC.VLHS| x) atbl)
                      (|LOGIC.FORMULA-ATBLP| (|LOGIC.VRHS| x) atbl)))
                ((equal type 'pnot*)
                 (|LOGIC.FORMULA-ATBLP| (|LOGIC.~ARG| x) atbl))
                ((equal type 'pequal*)
                 (and (|LOGIC.TERM-ATBLP| (|LOGIC.=LHS| x) atbl)
                      (|LOGIC.TERM-ATBLP| (|LOGIC.=RHS| x) atbl)))
                (t nil))))

       (|LOGIC.DISJOIN-FORMULAS| (x)
        (if (consp x)
            (if (consp (cdr x))
                (|LOGIC.POR| (car x) (|LOGIC.DISJOIN-FORMULAS| (cdr x)))
              (car x))
          nil))

       ;; THE PROOF CHECKER - APPEALS

       (|LOGIC.FLAG-APPEALP| (flag x)
        (if (equal flag 'proof)
            (and (true-listp x)
                 (<= (len x) 4)
                 (symbolp (first x))
                 (|LOGIC.FORMULAP| (second x))
                 (true-listp (third x))
                 (|LOGIC.FLAG-APPEALP| 'list (third x)))
          (if (consp x)
              (and (|LOGIC.FLAG-APPEALP| 'proof (car x))
                   (|LOGIC.FLAG-APPEALP| 'list (cdr x)))
            t)))

       (|LOGIC.APPEALP| (x) (|LOGIC.FLAG-APPEALP| 'proof x))
       (|LOGIC.APPEAL-LISTP| (x) (|LOGIC.FLAG-APPEALP| 'list x))

       (|LOGIC.METHOD| (x) (first x))
       (|LOGIC.CONCLUSION| (x) (second x))
       (|LOGIC.SUBPROOFS| (x) (third x))
       (|LOGIC.EXTRAS| (x) (fourth x))

       (|LOGIC.STRIP-CONCLUSIONS| (x)
        (if (consp x)
            (cons (|LOGIC.CONCLUSION| (car x))
                  (|LOGIC.STRIP-CONCLUSIONS| (cdr x)))
          nil))

       ;; THE PROOF CHECKER - STEP CHECKING

       (|LOGIC.AXIOM-OKP| (x axioms atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'axiom)
               (equal subproofs nil)
               (equal extras nil)
               (memberp conclusion axioms)
               (|LOGIC.FORMULA-ATBLP| conclusion atbl))))

       (|LOGIC.THEOREM-OKP| (x thms atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'theorem)
               (equal subproofs nil)
               (equal extras nil)
               (memberp conclusion thms)
               (|LOGIC.FORMULA-ATBLP| conclusion atbl))))

       ;; Basic Rules

       (|LOGIC.ASSOCIATIVITY-OKP| (x)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'associativity)
               (equal extras nil)
               (tuplep 1 subproofs)
               (let ((sub-or-a-or-b-c (|LOGIC.CONCLUSION| (first subproofs))))
                 (and (equal (|LOGIC.FMTYPE| conclusion) 'por*)
                      (equal (|LOGIC.FMTYPE| sub-or-a-or-b-c) 'por*)
                      (let ((conc-or-a-b (|LOGIC.VLHS| conclusion))
                            (conc-c      (|LOGIC.VRHS| conclusion))
                            (sub-a       (|LOGIC.VLHS| sub-or-a-or-b-c))
                            (sub-or-b-c  (|LOGIC.VRHS| sub-or-a-or-b-c)))
                        (and (equal (|LOGIC.FMTYPE| conc-or-a-b) 'por*)
                             (equal (|LOGIC.FMTYPE| sub-or-b-c) 'por*)
                             (let ((conc-a (|LOGIC.VLHS| conc-or-a-b))
                                   (conc-b (|LOGIC.VRHS| conc-or-a-b))
                                   (sub-b  (|LOGIC.VLHS| sub-or-b-c))
                                   (sub-c  (|LOGIC.VRHS| sub-or-b-c)))
                               (and (equal conc-a sub-a)
                                    (equal conc-b sub-b)
                                    (equal conc-c sub-c))))))))))

       (|LOGIC.CONTRACTION-OKP| (x)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'contraction)
               (equal extras nil)
               (tuplep 1 subproofs)
               (let ((or-a-a (|LOGIC.CONCLUSION| (first subproofs))))
                 (and (equal (|LOGIC.FMTYPE| or-a-a) 'por*)
                      (equal (|LOGIC.VLHS| or-a-a) conclusion)
                      (equal (|LOGIC.VRHS| or-a-a) conclusion))))))

       (|LOGIC.CUT-OKP| (x)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'cut)
               (equal extras nil)
               (tuplep 2 subproofs)
               (let ((or-a-b     (|LOGIC.CONCLUSION| (first subproofs)))
                     (or-not-a-c (|LOGIC.CONCLUSION| (second subproofs))))
                 (and (equal (|LOGIC.FMTYPE| or-a-b) 'por*)
                      (equal (|LOGIC.FMTYPE| or-not-a-c) 'por*)
                      (let ((a     (|LOGIC.VLHS| or-a-b))
                            (b     (|LOGIC.VRHS| or-a-b))
                            (not-a (|LOGIC.VLHS| or-not-a-c))
                            (c     (|LOGIC.VRHS| or-not-a-c)))
                        (and (equal (|LOGIC.FMTYPE| not-a) 'pnot*)
                             (equal (|LOGIC.~ARG| not-a) a)
                             (equal (|LOGIC.FMTYPE| conclusion) 'por*)
                             (equal (|LOGIC.VLHS| conclusion) b)
                             (equal (|LOGIC.VRHS| conclusion) c))))))))

       (|LOGIC.EXPANSION-OKP| (x atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'expansion)
               (equal extras nil)
               (tuplep 1 subproofs)
               (let ((b (|LOGIC.CONCLUSION| (first subproofs))))
                 (and (equal (|LOGIC.FMTYPE| conclusion) 'por*)
                      (equal (|LOGIC.VRHS| conclusion) b)
                      (|LOGIC.FORMULA-ATBLP| (|LOGIC.VLHS| conclusion) atbl))))))

       (|LOGIC.PROPOSITIONAL-SCHEMA-OKP| (x atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'propositional-schema)
               (equal subproofs nil)
               (equal extras nil)
               (equal (|LOGIC.FMTYPE| conclusion) 'por*)
               (let ((not-a (|LOGIC.VLHS| conclusion))
                     (a     (|LOGIC.VRHS| conclusion)))
                 (and (equal (|LOGIC.FMTYPE| not-a) 'pnot*)
                      (equal (|LOGIC.~ARG| not-a) a)
                      (|LOGIC.FORMULA-ATBLP| a atbl))))))

       (|LOGIC.CHECK-FUNCTIONAL-AXIOM| (x ti si)
        (if (equal (|LOGIC.FMTYPE| x) 'pequal*)
            (and (|LOGIC.FUNCTIONP| (|LOGIC.=LHS| x))
                 (|LOGIC.FUNCTIONP| (|LOGIC.=RHS| x))
                 (equal (|LOGIC.FUNCTION-NAME| (|LOGIC.=LHS| x))
                        (|LOGIC.FUNCTION-NAME| (|LOGIC.=RHS| x)))
                 (equal (|LOGIC.FUNCTION-ARGS| (|LOGIC.=LHS| x)) (rev ti))
                 (equal (|LOGIC.FUNCTION-ARGS| (|LOGIC.=RHS| x)) (rev si)))
          (and (equal (|LOGIC.FMTYPE| x) 'por*)
               (equal (|LOGIC.FMTYPE| (|LOGIC.VLHS| x)) 'pnot*)
               (equal (|LOGIC.FMTYPE| (|LOGIC.~ARG| (|LOGIC.VLHS| x))) 'pequal*)
               (|LOGIC.CHECK-FUNCTIONAL-AXIOM|
                (|LOGIC.VRHS| x)
                (cons (|LOGIC.=LHS| (|LOGIC.~ARG| (|LOGIC.VLHS| x))) ti)
                (cons (|LOGIC.=RHS| (|LOGIC.~ARG| (|LOGIC.VLHS| x))) si)))))

       (|LOGIC.FUNCTIONAL-EQUALITY-OKP| (x atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'functional-equality)
               (equal subproofs nil)
               (equal extras nil)
               (|LOGIC.CHECK-FUNCTIONAL-AXIOM| conclusion nil nil)
               (|LOGIC.FORMULA-ATBLP| conclusion atbl))))


       ;; Beta-Reduction, Instantiation

       (|LOGIC.SIGMAP| (x)
        (if (consp x)
            (and (consp (car x))
                 (|LOGIC.VARIABLEP| (car (car x)))
                 (|LOGIC.TERMP| (cdr (car x)))
                 (|LOGIC.SIGMAP| (cdr x)))
          t))

       (|LOGIC.SIGMA-LISTP| (x)
        (if (consp x)
            (and (|LOGIC.SIGMAP| (car x))
                 (|LOGIC.SIGMA-LISTP| (cdr x)))
          t))

       (|LOGIC.SIGMA-LIST-LISTP| (x)
        (if (consp x)
            (and (|LOGIC.SIGMA-LISTP| (car x))
                 (|LOGIC.SIGMA-LIST-LISTP| (cdr x)))
          t))

       (|LOGIC.FLAG-SUBSTITUTE| (flag x sigma)
        (if (equal flag 'term)
            (cond ((|LOGIC.VARIABLEP| x)
                   (if (lookup x sigma)
                       (cdr (lookup x sigma))
                     x))
                  ((|LOGIC.CONSTANTP| x)
                   x)
                  ((|LOGIC.FUNCTIONP| x)
                   (let ((fn   (|LOGIC.FUNCTION-NAME| x))
                         (args (|LOGIC.FUNCTION-ARGS| x)))
                     (|LOGIC.FUNCTION| fn (|LOGIC.FLAG-SUBSTITUTE|
                                           'list args sigma))))
                  ((|LOGIC.LAMBDAP| x)
                   (let ((formals (|LOGIC.LAMBDA-FORMALS| x))
                         (body    (|LOGIC.LAMBDA-BODY| x))
                         (actuals (|LOGIC.LAMBDA-ACTUALS| x)))
                     (|LOGIC.LAMBDA| formals body (|LOGIC.FLAG-SUBSTITUTE|
                                                   'list actuals sigma))))
                  (t nil))
          (if (consp x)
              (cons (|LOGIC.FLAG-SUBSTITUTE| 'term (car x) sigma)
                    (|LOGIC.FLAG-SUBSTITUTE| 'list (cdr x) sigma))
            nil)))

       (|LOGIC.SUBSTITUTE| (x sigma)
        (|LOGIC.FLAG-SUBSTITUTE| 'term x sigma))

       (|LOGIC.SUBSTITUTE-LIST| (x sigma)
        (|LOGIC.FLAG-SUBSTITUTE| 'list x sigma))

       (|LOGIC.SUBSTITUTE-FORMULA| (formula sigma)
        (let ((type (|LOGIC.FMTYPE| formula)))
          (cond ((equal type 'por*)
                 (|LOGIC.POR|
                  (|LOGIC.SUBSTITUTE-FORMULA| (|LOGIC.VLHS| formula) sigma)
                  (|LOGIC.SUBSTITUTE-FORMULA| (|LOGIC.VRHS| formula) sigma)))
                ((equal type 'pnot*)
                 (|LOGIC.PNOT|
                  (|LOGIC.SUBSTITUTE-FORMULA| (|LOGIC.~ARG| formula) sigma)))
                ((equal type 'pequal*)
                 (|LOGIC.PEQUAL|
                  (|LOGIC.SUBSTITUTE| (|LOGIC.=LHS| formula) sigma)
                  (|LOGIC.SUBSTITUTE| (|LOGIC.=RHS| formula) sigma)))
                (t nil))))

       (|LOGIC.INSTANTIATION-OKP| (x atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'instantiation)
               (|LOGIC.SIGMAP| extras)
               (tuplep 1 subproofs)
               (equal (|LOGIC.SUBSTITUTE-FORMULA|
                       (|LOGIC.CONCLUSION| (first subproofs)) extras)
                      conclusion)
               (|LOGIC.FORMULA-ATBLP| conclusion atbl))))

       (|LOGIC.BETA-REDUCTION-OKP| (x atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'beta-reduction)
               (equal subproofs nil)
               (equal extras nil)
               (|LOGIC.FORMULA-ATBLP| conclusion atbl)
               (equal (|LOGIC.FMTYPE| conclusion) 'pequal*)
               (let ((lhs (|LOGIC.=LHS| conclusion))
                     (rhs (|LOGIC.=RHS| conclusion)))
                 (and (|LOGIC.LAMBDAP| lhs)
                      (let ((formals (|LOGIC.LAMBDA-FORMALS| lhs))
                            (body    (|LOGIC.LAMBDA-BODY| lhs))
                            (actuals (|LOGIC.LAMBDA-ACTUALS| lhs)))
                        (equal (|LOGIC.SUBSTITUTE|
                                body (pair-lists formals actuals))
                               rhs)))))))

       ;; Base Evaluation

       (|LOGIC.INITIAL-ARITY-TABLE| ()
        '((if . 3)
          (equal . 2)
          (consp . 1)
          (cons . 2)
          (car . 1)
          (cdr . 1)
          (symbolp . 1)
          (symbol-< . 2)
          (natp . 1)
          (< . 2)
          (+ . 2)
          (- . 2)))

       (|LOGIC.BASE-EVALUABLEP| (x)
        (and (|LOGIC.FUNCTIONP| x)
             (let ((fn   (|LOGIC.FUNCTION-NAME| x))
                   (args (|LOGIC.FUNCTION-ARGS| x)))
               (let ((entry (lookup fn (|LOGIC.INITIAL-ARITY-TABLE|))))
                 (and entry
                      (|LOGIC.CONSTANT-LISTP| args)
                      (tuplep (cdr entry) args))))))

       (|LOGIC.BASE-EVALUATOR| (x)
        (let ((fn   (|LOGIC.FUNCTION-NAME| x))
              (vals (|LOGIC.UNQUOTE-LIST| (|LOGIC.FUNCTION-ARGS| x))))
          (list 'quote
                (cond ((equal fn 'if)
                       (if (first vals)
                           (second vals)
                         (third vals)))
                      ((equal fn 'equal)
                       (equal (first vals) (second vals)))
                      ((equal fn 'consp)
                       (consp (first vals)))
                      ((equal fn 'cons)
                       (cons (first vals) (second vals)))
                      ((equal fn 'car)
                       (car (first vals)))
                      ((equal fn 'cdr)
                       (cdr (first vals)))
                      ((equal fn 'symbolp)
                       (symbolp (first vals)))
                      ((equal fn 'symbol-<)
                       (symbol-< (first vals) (second vals)))
                      ((equal fn 'natp)
                       (natp (first vals)))
                      ((equal fn '<)
                       (< (first vals) (second vals)))
                      ((equal fn '+)
                       (+ (first vals) (second vals)))
                      ((equal fn '-)
                       (- (first vals) (second vals)))))))

       (|LOGIC.BASE-EVAL-OKP| (x atbl)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and (equal method 'base-eval)
               (equal subproofs nil)
               (equal extras nil)
               (equal (|LOGIC.FMTYPE| conclusion) 'pequal*)
               (let ((lhs (|LOGIC.=LHS| conclusion))
                     (rhs (|LOGIC.=RHS| conclusion)))
                 (and (|LOGIC.BASE-EVALUABLEP| lhs)
                      (equal (|LOGIC.BASE-EVALUATOR| lhs) rhs)
                      (|LOGIC.TERM-ATBLP| lhs atbl))))))


       ;; Induction

       (|LOGIC.MAKE-BASIS-STEP| (f qs)
        (|LOGIC.DISJOIN-FORMULAS| (cons f qs)))

       (|LOGIC.SUBSTITUTE-EACH-SIGMA-INTO-FORMULA| (f x)
        (if (consp x)
            (cons (|LOGIC.SUBSTITUTE-FORMULA| f (car x))
                  (|LOGIC.SUBSTITUTE-EACH-SIGMA-INTO-FORMULA| f (cdr x)))
          nil))

       (|LOGIC.MAKE-INDUCTION-STEP| (f q-i sigmas-i)
        (|LOGIC.DISJOIN-FORMULAS|
         (cons f (cons (|LOGIC.PNOT| q-i)
                       (|LOGIC.SUBSTITUTE-EACH-SIGMA-INTO-FORMULA|
                        (|LOGIC.PNOT| f) sigmas-i)))))

       (|LOGIC.MAKE-INDUCTION-STEPS| (f qs all-sigmas)
        (if (consp qs)
            (cons (|LOGIC.MAKE-INDUCTION-STEP| f (car qs) (car all-sigmas))
                  (|LOGIC.MAKE-INDUCTION-STEPS| f (cdr qs) (cdr all-sigmas)))
          nil))

       (|LOGIC.MAKE-ORDINAL-STEP| (m)
        (|LOGIC.PEQUAL| (|LOGIC.FUNCTION| 'ordp (list m)) ''t))

       (|LOGIC.MAKE-MEASURE-STEP| (m q-i sigma-i-j)
        (|LOGIC.POR|
         (|LOGIC.PNOT| q-i)
         (|LOGIC.PEQUAL|
          (|LOGIC.FUNCTION| 'ord< (list (|LOGIC.SUBSTITUTE| m sigma-i-j) m))
          ''t)))

       (|LOGIC.MAKE-MEASURE-STEPS| (m q-i sigmas-i)
        (if (consp sigmas-i)
            (cons (|LOGIC.MAKE-MEASURE-STEP| m q-i (car sigmas-i))
                  (|LOGIC.MAKE-MEASURE-STEPS| m q-i (cdr sigmas-i)))
          nil))

       (|LOGIC.MAKE-ALL-MEASURE-STEPS| (m qs all-sigmas)
        (if (consp all-sigmas)
            (app (|LOGIC.MAKE-MEASURE-STEPS| m (car qs) (car all-sigmas))
                 (|LOGIC.MAKE-ALL-MEASURE-STEPS| m (cdr qs) (cdr all-sigmas)))
          nil))

       (|LOGIC.INDUCTION-OKP| (x)
        (let ((method     (|LOGIC.METHOD| x))
              (conclusion (|LOGIC.CONCLUSION| x))
              (subproofs  (|LOGIC.SUBPROOFS| x))
              (extras     (|LOGIC.EXTRAS| x)))
          (and
           (equal method 'induction)
           (tuplep 3 extras)
           (let ((m          (first extras))
                 (qs         (second extras))
                 (all-sigmas (third extras))
                 (subconcs   (|LOGIC.STRIP-CONCLUSIONS| subproofs)))
             (and (|LOGIC.TERMP| m)
                  (|LOGIC.FORMULA-LISTP| qs)
                  (|LOGIC.SIGMA-LIST-LISTP| all-sigmas)
                  (equal (len qs) (len all-sigmas))
                  (memberp (|LOGIC.MAKE-BASIS-STEP| conclusion qs) subconcs)
                  (subsetp (|LOGIC.MAKE-INDUCTION-STEPS| conclusion qs all-sigmas)
                           subconcs)
                  (memberp (|LOGIC.MAKE-ORDINAL-STEP| m) subconcs)
                  (subsetp (|LOGIC.MAKE-ALL-MEASURE-STEPS| m qs all-sigmas)
                           subconcs))))))


       ;; Proof Checking

       (|LOGIC.APPEAL-STEP-OKP| (x axioms thms atbl)
        (let ((how (|LOGIC.METHOD| x)))
          (cond ((equal how 'axiom)
                 (|LOGIC.AXIOM-OKP| x axioms atbl))
                ((equal how 'theorem)
                 (|LOGIC.THEOREM-OKP| x thms atbl))
                ((equal how 'propositional-schema)
                 (|LOGIC.PROPOSITIONAL-SCHEMA-OKP| x atbl))
                ((equal how 'functional-equality)
                 (|LOGIC.FUNCTIONAL-EQUALITY-OKP| x atbl))
                ((equal how 'beta-reduction)
                 (|LOGIC.BETA-REDUCTION-OKP| x atbl))
                ((equal how 'expansion)
                 (|LOGIC.EXPANSION-OKP| x atbl))
                ((equal how 'contraction)
                 (|LOGIC.CONTRACTION-OKP| x))
                ((equal how 'associativity)
                 (|LOGIC.ASSOCIATIVITY-OKP| x))
                ((equal how 'cut)
                 (|LOGIC.CUT-OKP| x))
                ((equal how 'instantiation)
                 (|LOGIC.INSTANTIATION-OKP| x atbl))
                ((equal how 'induction)
                 (|LOGIC.INDUCTION-OKP| x))
                ((equal how 'base-eval)
                 (|LOGIC.BASE-EVAL-OKP| x atbl))
                (t nil))))

       (|LOGIC.FLAG-PROOFP| (flag x axioms thms atbl)
        (if (equal flag 'proof)
            (and (|LOGIC.APPEAL-STEP-OKP| x axioms thms atbl)
                 (|LOGIC.FLAG-PROOFP| 'list (|LOGIC.SUBPROOFS| x) axioms thms atbl))
          (if (consp x)
              (and (|LOGIC.FLAG-PROOFP| 'proof (car x) axioms thms atbl)
                   (|LOGIC.FLAG-PROOFP| 'list (cdr x) axioms thms atbl))
            t)))

       (|LOGIC.PROOFP| (x axioms thms atbl)
        (|LOGIC.FLAG-PROOFP| 'proof x axioms thms atbl))

       (|LOGIC.PROVABLE-WITNESS|
        (x axioms thms atbl)
        (error '(|LOGIC.PROVABLE-WITNESS|
                 proof
                 (x axioms thms atbl)
                 (and (|LOGIC.APPEALP| proof)
                      (|LOGIC.PROOFP| proof axioms thms atbl)
                      (equal (|LOGIC.CONCLUSION| proof) x)))))

       (|LOGIC.PROVABLEP| (x axioms thms atbl)
        (let ((proof (|LOGIC.PROVABLE-WITNESS| x axioms thms atbl)))
          (and (|LOGIC.APPEALP| proof)
               (|LOGIC.PROOFP| proof axioms thms atbl)
               (equal (|LOGIC.CONCLUSION| proof) x))))

       ;; SUPPORTING ABBREVIATIONS

       (remove-all (a x)
                   (if (consp x)
                       (if (equal a (car x))
                           (remove-all a (cdr x))
                         (cons (car x) (remove-all a (cdr x))))
                     nil))

       (remove-duplicates (x)
                          (if (consp x)
                              (if (memberp (car x) (cdr x))
                                  (remove-duplicates (cdr x))
                                (cons (car x) (remove-duplicates (cdr x))))
                            nil))

       (difference (x y)
                   (if (consp x)
                       (if (memberp (car x) y)
                           (difference (cdr x) y)
                         (cons (car x)
                               (difference (cdr x) y)))
                     nil))

       (strip-firsts (x)
                     (if (consp x)
                         (cons (first (car x))
                               (strip-firsts (cdr x)))
                       nil))

       (strip-seconds (x)
                      (if (consp x)
                          (cons (second (car x))
                                (strip-seconds (cdr x)))
                        nil))

       (tuple-listp (n x)
                    (if (consp x)
                        (and (tuplep n (car x))
                             (tuple-listp n (cdr x)))
                      t))

       (sort-symbols-insert
        (a x)
        (if (consp x)
            (if (symbol-< a (car x))
                (cons a x)
              (cons (car x)
                    (sort-symbols-insert a (cdr x))))
          (list a)))

       (sort-symbols
        (x)
        (if (consp x)
            (sort-symbols-insert (car x)
                                 (sort-symbols (cdr x)))
          nil))

       (|LOGIC.TRANSLATE-AND-TERM| (args)
        (if (consp args)
            (if (consp (cdr args))
                (|LOGIC.FUNCTION|
                 'if
                 (list (first args)
                       (|LOGIC.TRANSLATE-AND-TERM| (cdr args))
                       ''nil))
              (first args))
          ''t))

       (|LOGIC.TRANSLATE-LET-TERM| (vars terms body)
        (let* ((body-vars (remove-duplicates (|LOGIC.TERM-VARS| body)))
               (id-vars   (sort-symbols (difference body-vars vars)))
               (formals   (app id-vars vars))
               (actuals   (app id-vars terms)))
          (|LOGIC.LAMBDA| formals body actuals)))

       (|LOGIC.TRANSLATE-OR-TERM| (args)
        (if (consp args)
            (if (consp (cdr args))
                (let* ((else-term (|LOGIC.TRANSLATE-OR-TERM| (cdr args)))
                       (cheap-p   (or (|LOGIC.VARIABLEP| (car args))
                                      (|LOGIC.CONSTANTP| (car args)))))
                  (if (or cheap-p
                          (memberp 'special-var-for-or
                                   (|LOGIC.TERM-VARS| else-term)))
                      (|LOGIC.FUNCTION| 'if (list (car args) (car args) else-term))
                    (|LOGIC.TRANSLATE-LET-TERM|
                     (list 'special-var-for-or)
                     (list (car args))
                     (|LOGIC.FUNCTION| 'if (list 'special-var-for-or
                                                 'special-var-for-or
                                                 else-term)))))
              (first args))
          ''nil))

       (|LOGIC.TRANSLATE-LIST-TERM| (args)
        (if (consp args)
            (|LOGIC.FUNCTION|
             'cons
             (list (car args)
                   (|LOGIC.TRANSLATE-LIST-TERM| (cdr args))))
          ''nil))

       (|LOGIC.TRANSLATE-COND-TERM| (tests thens)
        (if (consp tests)
            (let ((test1 (car tests))
                  (then1 (car thens)))
              (|LOGIC.FUNCTION|
               'if
               (list test1
                     then1
                     (|LOGIC.TRANSLATE-COND-TERM| (cdr tests)
                                                  (cdr thens)))))
          ''nil))

       (|LOGIC.TRANSLATE-LET*-TERM| (vars terms body)
        (if (consp vars)
            (|LOGIC.TRANSLATE-LET-TERM|
             (list (car vars))
             (list (car terms))
             (|LOGIC.TRANSLATE-LET*-TERM| (cdr vars) (cdr terms) body))
          body))

       (|LOGIC.FLAG-TRANSLATE| (flag x)
        (if (equal flag 'term)
            (cond ((natp x)
                   (list 'quote x))
                  ((symbolp x)
                   (if (or (equal x nil)
                           (equal x t))
                       (list 'quote x)
                     x))
                  ((symbolp (car x))
                   (let ((fn (car x)))
                     (cond ((equal fn 'quote)
                            (if (tuplep 2 x)
                                x
                              nil))
                           ((memberp fn '(first second third fourth fifth))
                            (and (tuplep 2 x)
                                 (let ((arg (|LOGIC.FLAG-TRANSLATE| 'term (second x))))
                                   (and arg
                                        (let* ((|1CDR| (|LOGIC.FUNCTION| 'cdr (list arg)))
                                               (|2CDR| (|LOGIC.FUNCTION| 'cdr (list |1CDR|)))
                                               (|3CDR| (|LOGIC.FUNCTION| 'cdr (list |2CDR|)))
                                               (|4CDR| (|LOGIC.FUNCTION| 'cdr (list |3CDR|))))
                                          (|LOGIC.FUNCTION|
                                           'car
                                           (list (cond ((equal fn 'first)  arg)
                                                       ((equal fn 'second) |1CDR|)
                                                       ((equal fn 'third)  |2CDR|)
                                                       ((equal fn 'fourth) |3CDR|)
                                                       (t                  |4CDR|)))))))))
                           ((memberp fn '(and or list))
                            (and (true-listp (cdr x))
                                 (let ((arguments+ (|LOGIC.FLAG-TRANSLATE| 'list (cdr x))))
                                   (and (car arguments+)
                                        (cond ((equal fn 'and)
                                               (|LOGIC.TRANSLATE-AND-TERM| (cdr arguments+)))
                                              ((equal fn 'or)
                                               (|LOGIC.TRANSLATE-OR-TERM| (cdr arguments+)))
                                              (t
                                               (|LOGIC.TRANSLATE-LIST-TERM| (cdr arguments+))))))))
                           ((equal fn 'cond)
                            (and (true-listp (cdr x))
                                 (tuple-listp 2 (cdr x))
                                 (let* ((tests  (strip-firsts (cdr x)))
                                        (thens  (strip-seconds (cdr x)))
                                        (tests+ (|LOGIC.FLAG-TRANSLATE| 'list tests))
                                        (thens+ (|LOGIC.FLAG-TRANSLATE| 'list thens)))
                                   (and (car tests+)
                                        (car thens+)
                                        (|LOGIC.TRANSLATE-COND-TERM| (cdr tests+)
                                                                     (cdr thens+))))))
                           ((memberp fn '(let let*))
                            (and (tuplep 3 x)
                                 (let ((pairs (second x))
                                       (body  (|LOGIC.FLAG-TRANSLATE| 'term (third x))))
                                   (and body
                                        (true-listp pairs)
                                        (tuple-listp 2 pairs)
                                        (let* ((vars   (strip-firsts pairs))
                                               (terms  (strip-seconds pairs))
                                               (terms+ (|LOGIC.FLAG-TRANSLATE| 'list terms)))
                                          (and (car terms+)
                                               (|LOGIC.VARIABLE-LISTP| vars)
                                               (cond ((equal fn 'let)
                                                      (and (uniquep vars)
                                                           (|LOGIC.TRANSLATE-LET-TERM| vars
                                                                                       (cdr terms+)
                                                                                       body)))
                                                     (t
                                                      (|LOGIC.TRANSLATE-LET*-TERM| vars
                                                                                   (cdr terms+)
                                                                                   body)))))))))
                           ((|LOGIC.FUNCTION-NAMEP| fn)
                            (and (true-listp (cdr x))
                                 (let ((arguments+ (|LOGIC.FLAG-TRANSLATE| 'list (cdr x))))
                                   (and (car arguments+)
                                        (|LOGIC.FUNCTION| fn (cdr arguments+))))))
                           (t
                            nil))))
                  ((and (tuplep 3 (car x))
                        (true-listp (cdr x)))
                   (let* ((lambda-symbol (first (car x)))
                          (vars          (second (car x)))
                          (body          (third (car x)))
                          (new-body      (|LOGIC.FLAG-TRANSLATE| 'term body))
                          (actuals+      (|LOGIC.FLAG-TRANSLATE| 'list (cdr x))))
                     (and (equal lambda-symbol 'lambda)
                          (true-listp vars)
                          (|LOGIC.VARIABLE-LISTP| vars)
                          (uniquep vars)
                          new-body
                          (subsetp (|LOGIC.TERM-VARS| new-body) vars)
                          (car actuals+)
                          (equal (len vars) (len (cdr actuals+)))
                          (|LOGIC.LAMBDA| vars new-body (cdr actuals+)))))
                  (t
                   nil))
          (if (consp x)
              (let ((first (|LOGIC.FLAG-TRANSLATE| 'term (car x)))
                    (rest  (|LOGIC.FLAG-TRANSLATE| 'list (cdr x))))
                (if (and first (car rest))
                    (cons t (cons first (cdr rest)))
                  (cons nil nil)))
            (cons t nil))))

       (|LOGIC.TRANSLATE| (x) (|LOGIC.FLAG-TRANSLATE| 'term x))


       ;; TERMINATION OBLIGATIONS

       (cons-onto-ranges
        (a x)
        (if (consp x)
            (cons (cons (car (car x))
                        (cons a (cdr (car x))))
                  (cons-onto-ranges a (cdr x)))
          nil))

       (|LOGIC.SUBSTITUTE-CALLMAP|
        (x sigma)
        (if (consp x)
            (let ((actuals (car (car x)))
                  (rulers  (cdr (car x))))
              (cons (cons (|LOGIC.SUBSTITUTE-LIST| actuals sigma)
                          (|LOGIC.SUBSTITUTE-LIST| rulers sigma))
                    (|LOGIC.SUBSTITUTE-CALLMAP| (cdr x) sigma)))
          nil))

       (|LOGIC.FLAG-CALLMAP|
        (flag f x)
        (if (equal flag 'term)
            (cond ((|LOGIC.CONSTANTP| x)
                   nil)
                  ((|LOGIC.VARIABLEP| x)
                   nil)
                  ((|LOGIC.FUNCTIONP| x)
                   (let ((name (|LOGIC.FUNCTION-NAME| x))
                         (args (|LOGIC.FUNCTION-ARGS| x)))
                     (cond ((and (equal name 'if)
                                 (equal (len args) 3))
                            (let ((test-calls
                                   (|LOGIC.FLAG-CALLMAP| 'term f (first args)))
                                  (true-calls
                                   (cons-onto-ranges
                                    (first args)
                                    (|LOGIC.FLAG-CALLMAP| 'term f (second args))))
                                  (else-calls
                                   (cons-onto-ranges
                                    (|LOGIC.FUNCTION| 'not (list (first args)))
                                    (|LOGIC.FLAG-CALLMAP| 'term f (third args)))))
                              (app test-calls (app true-calls else-calls))))
                           ((equal name f)
                            (let ((this-call   (cons args nil))
                                  (child-calls (|LOGIC.FLAG-CALLMAP| 'list f args)))
                              (cons this-call child-calls)))
                           (t
                            (|LOGIC.FLAG-CALLMAP| 'list f args)))))
                  ((|LOGIC.LAMBDAP| x)
                   (let ((formals (|LOGIC.LAMBDA-FORMALS| x))
                         (body    (|LOGIC.LAMBDA-BODY| x))
                         (actuals (|LOGIC.LAMBDA-ACTUALS| x)))
                     (let ((actuals-calls (|LOGIC.FLAG-CALLMAP| 'list f actuals))
                           (body-calls    (|LOGIC.FLAG-CALLMAP| 'term f body))
                           (sigma         (pair-lists formals actuals)))
                       (app actuals-calls
                            (|LOGIC.SUBSTITUTE-CALLMAP| body-calls sigma))))))
          (if (consp x)
              (app (|LOGIC.FLAG-CALLMAP| 'term f (car x))
                   (|LOGIC.FLAG-CALLMAP| 'list f (cdr x)))
            nil)))

       (|LOGIC.CALLMAP| (f x)
        (|LOGIC.FLAG-CALLMAP| 'term f x))

       (repeat (a n)
               (if (zp n)
                   nil
                 (cons a (repeat a (- n 1)))))

       (|LOGIC.PEQUAL-LIST| (x y)
        (if (and (consp x)
                 (consp y))
            (cons (|LOGIC.PEQUAL| (car x) (car y))
                  (|LOGIC.PEQUAL-LIST| (cdr x) (cdr y)))
          nil))

       (|LOGIC.PROGRESS-OBLIGATION| (measure formals actuals rulers)
        (let* ((sigma     (pair-lists formals actuals))
               (|M/SIGMA| (|LOGIC.SUBSTITUTE| measure sigma))
               (ord-term  (|LOGIC.FUNCTION| 'ord< (list |M/SIGMA| measure))))
          (|LOGIC.DISJOIN-FORMULAS|
           (cons (|LOGIC.PEQUAL| ord-term ''t)
                 (|LOGIC.PEQUAL-LIST| rulers (repeat ''nil (len rulers)))))))

       (|LOGIC.PROGRESS-OBLIGATIONS|
        (measure formals callmap)
        (if (consp callmap)
            (let* ((entry   (car callmap))
                   (actuals (car entry))
                   (rulers  (cdr entry)))
              (cons (|LOGIC.PROGRESS-OBLIGATION| measure formals actuals rulers)
                    (|LOGIC.PROGRESS-OBLIGATIONS| measure formals (cdr callmap))))
          nil))

       (|LOGIC.TERMINATION-OBLIGATIONS|
        (name formals body measure)
        (let ((callmap (|LOGIC.CALLMAP| name body)))
          (if callmap
              (cons (|LOGIC.PEQUAL| (|LOGIC.FUNCTION| 'ordp (list measure)) ''t)
                    (|LOGIC.PROGRESS-OBLIGATIONS| measure formals callmap))
            nil)))


       (|CORE.INITIAL-ATBL| ()
        (app '((not . 1)
               (rank . 1)
               (ordp . 1)
               (ord< . 2))
             (|LOGIC.INITIAL-ARITY-TABLE|)))

       (|CORE.INITIAL-AXIOMS| ()
        (app '( ;; reflexivity
               (pequal* x x)

               ;; equality
               (por* (pnot* (pequal* x1 y1))
                     (por* (pnot* (pequal* x2 y2))
                           (por* (pnot* (pequal* x1 x2))
                                 (pequal* y1 y2))))

               ;; t-not-nil
               (pnot* (pequal* 't 'nil))

               ;; equal-when-same
               (por* (pnot* (pequal* x y))
                     (pequal* (equal x y) 't))

               ;; equal-when-diff
               (por* (pequal* x y)
                     (pequal* (equal x y) 'nil))

               ;; if-when-nil
               (por* (pnot* (pequal* x 'nil))
                     (pequal* (if x y z) z))

               ;; if-when-not-nil
               (por* (pequal* x 'nil)
                     (pequal* (if x y z) y))

               ;; consp-of-cons
               (pequal* (consp (cons x y)) 't)

               ;; car-of-cons
               (pequal* (car (cons x y)) x)

               ;; cdr-of-cons
               (pequal* (cdr (cons x y)) y)

               ;; consp-nil-or-t
               (por* (pequal* (consp x) 'nil)
                     (pequal* (consp x) 't))

               ;; car-when-not-consp
               (por* (pnot* (pequal* (consp x) 'nil))
                     (pequal* (car x) 'nil))

               ;; cdr-when-not-consp
               (por* (pnot* (pequal* (consp x) 'nil))
                     (pequal* (cdr x) 'nil))

               ;; cons-of-car-and-cdr
               (por* (pequal* (consp x) 'nil)
                     (pequal* (cons (car x) (cdr x)) x))

               ;; symbolp-nil-or-t
               (por* (pequal* (symbolp x) 'nil)
                     (pequal* (symbolp x) 't))

               ;; symbol-<-nil-or-t
               (por* (pequal* (symbol-< x y) 'nil)
                     (pequal* (symbol-< x y) 't))

               ;; irreflexivity-of-symbol-<
               (pequal* (symbol-< x x) 'nil)

               ;; antisymmetry-of-symbol-<
               (por* (pequal* (symbol-< x y) 'nil)
                     (pequal* (symbol-< y x) 'nil))

               ;; transitivity-of-symbol-<
               (por* (pequal* (symbol-< x y) 'nil)
                     (por* (pequal* (symbol-< y z) 'nil)
                           (pequal* (symbol-< x z) 't)))

               ;; trichotomy-of-symbol-<
               (por* (pequal* (symbolp x) 'nil)
                     (por* (pequal* (symbolp y) 'nil)
                           (por* (pequal* (symbol-< x y) 't)
                                 (por* (pequal* (symbol-< y x) 't)
                                       (pequal* x y)))))

               ;; symbol-<-completion-left
               (por* (pequal* (symbolp x) 't)
                     (pequal* (symbol-< x y)
                              (symbol-< 'nil y)))

               ;; symbol-<-completion-right
               (por* (pequal* (symbolp y) 't)
                     (pequal* (symbol-< x y)
                              (symbol-< x 'nil)))

               ;; disjoint-symbols-and-naturals
               (por* (pequal* (symbolp x) 'nil)
                     (pequal* (natp x) 'nil))

               ;; disjoint-symbols-and-conses
               (por* (pequal* (symbolp x) 'nil)
                     (pequal* (consp x) 'nil))

               ;; disjoint-naturals-and-conses
               (por* (pequal* (natp x) 'nil)
                     (pequal* (consp x) 'nil))

               ;; natp-nil-or-t
               (por* (pequal* (natp x) 'nil)
                     (pequal* (natp x) 't))

               ;; natp-of-plus
               (pequal* (natp (+ a b)) 't)

               ;; commutativity-of-+
               (pequal* (+ a b) (+ b a))

               ;; associativity-of-+
               (pequal* (+ (+ a b) c)
                        (+ a (+ b c)))

               ;; plus-when-not-natp-left
               (por* (pequal* (natp a) 't)
                     (pequal* (+ a b) (+ '0 b)))

               ;; plus-of-zero-when-natural
               (por* (pequal* (natp a) 'nil)
                     (pequal* (+ a '0) a))

               ;; <-nil-or-t
               (por* (pequal* (< x y) 'nil)
                     (pequal* (< x y) 't))

               ;; irreflexivity-of-<
               (pequal* (< a a) 'nil)

               ;; less-of-zero-right
               (pequal* (< a '0) 'nil)

               ;; less-of-zero-left-when-natp
               (por* (pequal* (natp a) 'nil)
                     (pequal* (< '0 a)
                              (if (equal a '0) 'nil 't)))

               ;; less-completion-left
               (por* (pequal* (natp a) 't)
                     (pequal* (< a b)
                              (< '0 b)))

               ;; less-completion-right
               (por* (pequal* (natp b) 't)
                     (pequal* (< a b)
                              'nil))

               ;; transitivity-of-<
               (por* (pequal* (< a b) 'nil)
                     (por* (pequal* (< b c) 'nil)
                           (pequal* (< a c) 't)))

               ;; trichotomy-of-<-when-natp
               (por* (pequal* (natp a) 'nil)
                     (por* (pequal* (natp b) 'nil)
                           (por* (pequal* (< a b) 't)
                                 (por* (pequal* (< b a) 't)
                                       (pequal* a b)))))

               ;; one-plus-trick
               (por* (pequal* (< a b) 'nil)
                     (pequal* (< b (+ '1 a)) 'nil))

               ;; natural-less-than-one-is-zero
               (por* (pequal* (natp a) 'nil)
                     (por* (pequal* (< a '1) 'nil)
                           (pequal* a '0)))

               ;; less-than-of-plus-and-plus
               (pequal* (< (+ a b) (+ a c))
                        (< b c))

               ;; natp-of-minus
               (pequal* (natp (- a b)) 't)

               ;; minus-when-subtrahend-as-large
               (por* (pequal* (< b a) 't)
                     (pequal* (- a b) '0))

               ;; minus-cancels-summand-right
               (pequal* (- (+ a b) b)
                        (if (natp a) a '0))

               ;; less-of-minus-left
               (por* (pequal* (< b a) 'nil)
                     (pequal* (< (- a b) c)
                              (< a (+ b c))))

               ;; less-of-minus-right
               (pequal* (< a (- b c))
                        (< (+ a c) b))

               ;; plus-of-minus-right
               (por* (pequal* (< c b) 'nil)
                     (pequal* (+ a (- b c))
                              (- (+ a b) c)))

               ;; minus-of-minus-right
               (por* (pequal* (< c b) 'nil)
                     (pequal* (- a (- b c))
                              (- (+ a c) b)))

               ;; minus-of-minus-left
               (pequal* (- (- a b) c)
                        (- a (+ b c)))

               ;; equal-of-minus-property
               (por* (pequal* (< b a) 'nil)
                     (pequal* (equal (- a b) c)
                              (equal a (+ b c))))

               ;; closed-universe
               (por* (pequal* (natp x) 't)
                     (por* (pequal* (symbolp x) 't)
                           (pequal* (consp x) 't))))

             (list
              ;; definition-of-not
              (|LOGIC.PEQUAL| '(not x)
               (|LOGIC.TRANSLATE| '(if x nil t)))

              ;; definition-of-rank
              (|LOGIC.PEQUAL| '(rank x)
               (|LOGIC.TRANSLATE| '(if (consp x)
                                       (+ 1
                                          (+ (rank (car x))
                                             (rank (cdr x))))
                                     0)))

              ;; definition-of-ord<
              (|LOGIC.PEQUAL| '(ord< x y)
               (|LOGIC.TRANSLATE| '(cond ((not (consp x))
                                          (if (consp y)
                                              t
                                            (< x y)))
                                         ((not (consp y))
                                          nil)
                                         ((not (equal (car (car x))
                                                      (car (car y))))
                                          (ord< (car (car x))
                                                (car (car y))))
                                         ((not (equal (cdr (car x))
                                                      (cdr (car y))))
                                          (< (cdr (car x))
                                             (cdr (car y))))
                                         (t
                                          (ord< (cdr x) (cdr y))))))

              ;; definition-of-ordp
              (|LOGIC.PEQUAL| '(ordp x)
               (|LOGIC.TRANSLATE| '(if (not (consp x))
                                       (natp x)
                                     (and (consp (car x))
                                          (ordp (car (car x)))
                                          (not (equal (car (car x)) 0))
                                          (< 0 (cdr (car x)))
                                          (ordp (cdr x))
                                          (if (consp (cdr x))
                                              (ord< (car (car (cdr x)))
                                                    (car (car x)))
                                            t))))))))

       (|CORE.STATE| (axioms thms atbl checker ftbl)
        (list axioms thms atbl checker ftbl))

       (|CORE.AXIOMS|  (x) (first x))
       (|CORE.THMS|    (x) (second x))
       (|CORE.ATBL|    (x) (third x))
       (|CORE.CHECKER| (x) (fourth x))
       (|CORE.FTBL|    (x) (fifth x))

       (|CORE.CHECK-PROOF|
        (checker proof axioms thms atbl)
        (funcall checker proof axioms thms atbl))

       (|CORE.CHECK-PROOF-LIST|
        (checker proofs axioms thms atbl)
        (if (consp proofs)
            (and (|CORE.CHECK-PROOF| checker (car proofs) axioms thms atbl)
                 (|CORE.CHECK-PROOF-LIST| checker (cdr proofs) axioms thms atbl))
          t))

       (|LOGIC.SOUNDNESS-CLAIM|
        (name)
        (|LOGIC.POR|
         '(pequal* (|LOGIC.APPEALP| x) 'nil)
         (|LOGIC.POR|
          (|LOGIC.PEQUAL| (|LOGIC.FUNCTION| name '(x axioms thms atbl))
                        ''nil)
          '(pnot* (pequal* (|LOGIC.PROVABLEP| (|LOGIC.CONCLUSION| x)
                                              axioms thms atbl)
                           'nil)))))

       (|CORE.ADMIT-SWITCH|
        (cmd state)
        ;; Returns a new state or calls error.
        ;; CMD should be (SWITCH NAME)
        (if (or (not (tuplep 2 cmd))
                (not (equal (first cmd) 'switch)))
            (error (list 'admit-switch 'invalid-cmd cmd))
          (let ((axioms  (|CORE.AXIOMS| state))
                (thms    (|CORE.THMS| state))
                (atbl    (|CORE.ATBL| state))
                (ftbl    (|CORE.FTBL| state))
                (name    (second cmd)))
            (cond ((not (|LOGIC.FUNCTION-NAMEP| name))
                   (error (list 'admit-switch 'invalid-name name)))
                  ((not (memberp (|LOGIC.SOUNDNESS-CLAIM| name)
                                 (|CORE.THMS| state)))
                   (error (list 'admit-switch 'not-verified name)))
                  (t
                   (|CORE.STATE| axioms thms atbl name ftbl))))))

       (|CORE.ADMIT-THEOREM|
        (cmd state)
        ;; Returns a new state or calls error.
        ;; CMD should be (VERIFY NAME FORMULA PROOF)
        (if (or (not (tuplep 4 cmd))
                (not (equal (first cmd) 'verify)))
            (error (list 'admit-theorem 'invalid-cmd cmd))
          (let ((axioms  (|CORE.AXIOMS| state))
                (thms    (|CORE.THMS| state))
                (atbl    (|CORE.ATBL| state))
                (checker (|CORE.CHECKER| state))
                (ftbl    (|CORE.FTBL| state))
                (name    (second cmd))
                (formula (third cmd))
                (proof   (fourth cmd)))
            (cond
             ((not (|LOGIC.FORMULAP| formula))
              (error (list 'admit-theorem 'not-formulap name)))
             ((not (|LOGIC.FORMULA-ATBLP| formula atbl))
              (error (list 'admit-theorem 'not-formula-atblp
                           name formula atbl)))
             ((not (|LOGIC.APPEALP| proof))
              (error (list 'admit-theorem 'not-appealp name)))
             ((not (equal (|LOGIC.CONCLUSION| proof) formula))
              (error (list 'admit-theorem 'wrong-conclusion name)))
             ((not (|CORE.CHECK-PROOF| checker proof axioms thms atbl))
              (error (list 'admit-theorem 'proof-rejected name)))
             (t
              (if (memberp formula thms)
                  state
                (|CORE.STATE| axioms (cons formula thms) atbl checker ftbl)))))))

       (|CORE.ADMIT-DEFUN|
        (cmd state)
        ;; Returns a new state or calls error.
        ;; CMD should be (DEFINE NAME FORMALS BODY MEASURE PROOF-LIST)
        (if (or (not (tuplep 6 cmd))
                (not (equal (car cmd) 'define)))
            (error (list 'admit-defun 'invalid-cmd cmd))
          (let* ((axioms      (|CORE.AXIOMS| state))
                 (thms        (|CORE.THMS| state))
                 (atbl        (|CORE.ATBL| state))
                 (checker     (|CORE.CHECKER| state))
                 (ftbl        (|CORE.FTBL| state))
                 (name        (second cmd))
                 (formals     (third cmd))
                 (raw-body    (fourth cmd))
                 (raw-measure (fifth cmd))
                 (proofs      (fifth (cdr cmd)))
                 (body        (|LOGIC.TRANSLATE| raw-body))
                 (measure     (|LOGIC.TRANSLATE| raw-measure))
                 (arity       (len formals))
                 (new-atbl    (cons (cons name arity) atbl))
                 (obligations (|LOGIC.TERMINATION-OBLIGATIONS|
                               name formals body measure)))
            (cond ((not (|LOGIC.FUNCTION-NAMEP| name))
                   (error (list 'admit-defun 'bad-name name)))
                  ((not (true-listp formals))
                   (error (list 'admit-defun 'bad-formals name)))
                  ((not (|LOGIC.VARIABLE-LISTP| formals))
                   (error (list 'admit-defun 'bad-formals name)))
                  ((not (uniquep formals))
                   (error (list 'admit-defun 'duplicated-formals name)))
                  ((not (|LOGIC.TERMP| body))
                   (error (list 'admit-defun 'bad-body name
                                body raw-body cmd)))
                  ((not (|LOGIC.TERMP| measure))
                   (error (list 'admit-defun 'bad-measure name)))
                  ((not (subsetp (|LOGIC.TERM-VARS| body) formals))
                   (error (list 'admit-defun 'free-vars-in-body name)))
                  ((not (subsetp (|LOGIC.TERM-VARS| measure) formals))
                   (error (list 'admit-defun 'free-vars-in-measure name)))
                  ((not (|LOGIC.TERM-ATBLP| body new-atbl))
                   (error (list 'admit-defun 'bad-arity-in-body name)))
                  ((not (|LOGIC.TERM-ATBLP| measure new-atbl))
                   (error (list 'admit-defun 'bad-arity-in-measure name)))
                  ((not (|LOGIC.APPEAL-LISTP| proofs))
                   (error (list 'admit-defun 'proofs-not-appeals name)))
                  ((not (equal (|LOGIC.STRIP-CONCLUSIONS| proofs) obligations))
                   (error (list 'admit-defun 'proofs-wrong-conclusions name)))
                  ((not (|CORE.CHECK-PROOF-LIST| checker proofs axioms thms new-atbl))
                   (error (list 'admit-defun 'proof-rejected name)))
                  (t
                   (let* ((ftbl      (define-safe ftbl name formals raw-body))
                          (new-axiom (|LOGIC.PEQUAL| (|LOGIC.FUNCTION| name formals) body))
                          (atbl      (if (lookup name atbl)
                                         atbl
                                       new-atbl))
                          (axioms    (if (memberp new-axiom axioms)
                                         axioms
                                       (cons new-axiom axioms))))
                     (|CORE.STATE| axioms thms atbl checker ftbl)))))))

       (|CORE.ADMIT-WITNESS|
        (cmd state)
        ;; Returns a new state or calls error
        ;; CMD should be (SKOLEM NAME BOUND-VAR FREE-VAR BODY)
        (if (or (not (tuplep 5 cmd))
                (not (equal (car cmd) 'skolem)))
            (error (list 'admit-witness 'invalid-cmd cmd))
          (let* ((axioms    (|CORE.AXIOMS| state))
                 (thms      (|CORE.THMS| state))
                 (atbl      (|CORE.ATBL| state))
                 (checker   (|CORE.CHECKER| state))
                 (ftbl      (|CORE.FTBL| state))
                 (name      (second cmd))
                 (bound-var (third cmd))
                 (free-vars (fourth cmd))
                 (raw-body  (fifth cmd))
                 (body      (|LOGIC.TRANSLATE| raw-body))
                 (all-vars  (cons bound-var free-vars)))
            (cond
             ((not (|LOGIC.FUNCTION-NAMEP| name))
              (error (list 'admit-witness 'bad-name name)))
             ((not (true-listp free-vars))
              (error (list 'admit-witness 'bad-formals name)))
             ((not (|LOGIC.VARIABLEP| bound-var))
              (error (list 'admit-witness 'bad-bound-var name)))
             ((not (|LOGIC.VARIABLE-LISTP| free-vars))
              (error (list 'admit-witness 'bad-free-vars name)))
             ((not (uniquep (cons bound-var free-vars)))
              (error (list 'admit-witness 'duplicate-free-vars name)))
             ((not (|LOGIC.TERMP| body))
              (error (list 'admit-witness 'bad-body name)))
             ((not (subsetp (|LOGIC.TERM-VARS| body) all-vars))
              (error (list 'admit-witness 'free-vars-in-body name)))
             ((not (|LOGIC.TERM-ATBLP| body atbl))
              (error (list 'admit-witness 'bad-arity-in-body name)))
             (t
              (let* ((ftbl (define-safe ftbl name free-vars
                             (list 'error
                                   (list 'quote
                                         (list name bound-var
                                               free-vars raw-body)))))
                     (atbl (if (lookup name atbl)
                               atbl
                             (cons (cons name (len free-vars)) atbl)))
                     (new-axiom
                      (|LOGIC.POR| (|LOGIC.PEQUAL| body ''nil)
                                 (|LOGIC.PNOT|
                                  (|LOGIC.PEQUAL|
                                   (|LOGIC.LAMBDA|
                                    all-vars body
                                    (cons (|LOGIC.FUNCTION| name free-vars)
                                          free-vars))
                                   ''nil))))
                     (axioms (if (memberp new-axiom axioms)
                                 axioms
                               (cons new-axiom axioms))))
                (|CORE.STATE| axioms thms atbl checker ftbl)))))))

       (|CORE.EVAL-FUNCTION| (x)
        (let* ((fn        (|LOGIC.FUNCTION-NAME| x))
               (vals      (|LOGIC.UNQUOTE-LIST| (|LOGIC.FUNCTION-ARGS| x)))
               (n   (len vals))
               (x1  (first vals))
               (x2  (second vals))
               (x3  (third vals))
               (x4  (fourth vals))
               (x5  (fifth vals)))
            (list 'quote
                 (cond ((equal n 0) (funcall fn))
                       ((equal n 1) (funcall fn x1))
                       ((equal n 2) (funcall fn x1 x2))
                       ((equal n 3) (funcall fn x1 x2 x3))
                       ((equal n 4) (funcall fn x1 x2 x3 x4))
                       ((equal n 5) (funcall fn x1 x2 x3 x4 x5))
                       (t (error (list 'core-eval-function 'too-many-parameters)))))))

       (|CORE.ADMIT-EVAL|
        (cmd state)
        ;; Performs evaluation in the runtime
        ;; CMD should be (EVAL (fn 'arg1 'arg2 ... 'argN))
        (let* ((axioms    (|CORE.AXIOMS| state))
               (thms      (|CORE.THMS| state))
               (atbl      (|CORE.ATBL| state))
               (checker   (|CORE.CHECKER| state))
               (ftbl      (|CORE.FTBL| state))
               (lhs       (second cmd)))
            (cond
              ((not (|LOGIC.TERMP| lhs))
               (error (list 'admit-eval 'bad-term-on-lhs lhs)))
              ((not (|LOGIC.FUNCTIONP| lhs))
               (error (list 'admit-eval 'not-function-on-lhs lhs)))
              ((not (|LOGIC.CONSTANT-LISTP| (|LOGIC.FUNCTION-ARGS| lhs)))
               (error (list 'admit-eval 'not-const-list-on-lhs lhs)))
              ((not (|LOGIC.TERM-ATBLP| lhs atbl))
               (error (list 'admit-eval 'bad-arity-on-lhs lhs)))
              ((lookup (|LOGIC.FUNCTION-NAME| lhs) (|CORE.INITIAL-ATBL|))
               (error (list 'admit-eval 'not-user-defined-function lhs)))
              (t
               (let* ((rhs      (|CORE.EVAL-FUNCTION| lhs))
                      (new-thm  (|LOGIC.PEQUAL| lhs rhs))
                      (thms     (cons new-thm thms)))
                  (|CORE.STATE| axioms thms atbl checker ftbl))))))

       (|CORE.ADMIT-PRINT|
        (cmd state)
        ;; Prints a theorem and returns original state, or calls error
        ;; CMD should be (PRINT FORMULA)
        (if (or (not (tuplep 2 cmd))
                (not (equal (car cmd) 'print)))
            (error (list 'admit-print 'invalid-cmd cmd))
          (let* ((axioms    (|CORE.AXIOMS| state))
                 (thms      (|CORE.THMS| state))
                 (formula   (second cmd)))
            (cond
             ((not (or (memberp formula axioms)
                       (memberp formula thms)))
              (error (list 'admit-print 'no-such-theorem)))
             (t (let* ((unused (print (list 'theorem formula))))
                   state))))))

       (|CORE.ACCEPT-COMMAND|
        (cmd state)
        ;; Returns a new state or calls error
        (cond ((equal (car cmd) 'verify) (|CORE.ADMIT-THEOREM| cmd state))
              ((equal (car cmd) 'define) (|CORE.ADMIT-DEFUN| cmd state))
              ((equal (car cmd) 'skolem) (|CORE.ADMIT-WITNESS| cmd state))
              ((equal (car cmd) 'switch) (|CORE.ADMIT-SWITCH| cmd state))
              ((equal (car cmd) 'print)  (|CORE.ADMIT-PRINT| cmd state))
              ((equal (car cmd) 'eval)   (|CORE.ADMIT-EVAL| cmd state))
              (t
               (error (list 'accept-cmd 'invalid-command cmd)))))

       (|CORE.ACCEPT-COMMANDS|
        (cmds event-number state)
        ;; Returns a new state or calls error.
        (if (consp cmds)
            (let* ((unused (print (list event-number
                                        (first (car cmds))
                                        (second (car cmds)))))
                    (state (|CORE.ACCEPT-COMMAND| (car cmds) state)))
              (|CORE.ACCEPT-COMMANDS| (cdr cmds)
                                    (+ 1 event-number)
                                    state))
          state))

       )))

(define 'milawa-main '(cmds)
  '(let* ((ftbl      (milawa-init))
          (axioms    (|CORE.INITIAL-AXIOMS|))
          (thms      'nil)
          (atbl      (|CORE.INITIAL-ATBL|))
          (checker   '|LOGIC.PROOFP|)
          (state     (|CORE.STATE| axioms thms atbl checker ftbl)))
     (and (|CORE.ACCEPT-COMMANDS| cmds '1 state)
          'success)))
