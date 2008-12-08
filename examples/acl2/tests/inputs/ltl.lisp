(in-package "ACL2")

;; The following two lines are added for portability to v2-7....


#|

  ltl.lisp
  ~~~~~~~~

In this book, we discuss the syntax of LTL formula and its semantics with
respect to a Kripke Structure. The standard semantics of LTL involve operations
with respect to an inifinitary object, namely the path. However, ACL2 does not
allow such objects. Thus, we need to define the semantics of LTL with respect
to a Kripke Structure directly. However, this requires a tableau construction
which is easy to get wrong and harder to prove theorems about, even if
specified correctly.

We have chosen to take a middle ground based on (John Matthews's)
discussions with Ernie Cohen. The idea is to define the semantics of LTL with
respect to eventually periodic paths. (We defer the proof now that any
verification of semantics over eventually periodic paths corresponds to a
verification over infinite paths and this might not be possible to do in
ACL2.) However, for the moment the semantics are with respect to eventually
periodic paths and the semantics for a Kripke Structure are given by
quantifying over all compatible paths.

The current book is produced to prove compositional reductions for
model-checking. The goal is to verify that the composition reductions are
correct given that the underlying model-checking routines are correct. Given
this assumption, we take further liberties and encapsulate the ltl semantics
over periodic paths as an underlying model-checking routine, exporting theorems
that are required to verify the reductions. The point in the case is that if
for a real LTL semantics function these constraints are not satisfied for
periodic paths, then the functions (and not the theorems) need to be changed,
making encapsulate a viable option in order to not get bogged down in
implementation of a model-checking routine for ltl. 

Questions and comments are welcome. -- Sandip.

|#

(set-match-free-default :once)

(include-book "sets")




;; We now define the syntax of an LTL formula. For purpose of reductions, we
;; also define a restricted formula over a subset of variables.

(defun ltl-constantp (f)
  (or (equal f 'true)
      (equal f 'false)))

(defun ltl-variablep (f)
  (and (symbolp f)
       (not (memberp f '(+ & U W X F G)))))

;; So an LTL formula is either (i) a constant 'True or 'False, (ii) a variable
;; which is a quote or a symbol other than the LTL operator symbol, or of the
;; form (P + Q), (P & Q), (P U Q), (P W Q), (~ P), (F P), (G P), (X P), where P
;; and Q are LTL formulas.


(defun ltl-formulap (f)
  (cond ((atom f) (or (ltl-constantp f)
                      (ltl-variablep f)))
        ((equal (len f) 3)
         (and (memberp (second f) '(+ & U W))
              (ltl-formulap (first f))
              (ltl-formulap (third f))))
        ((equal (len f) 2)
         (and (memberp (first f) '(~ X F G))
              (ltl-formulap (second f))))
        (t nil)))

;; A formula is called resctricted with respect to a collection vars of
;; variables if it mentions no variable other than those in vars. Here is the
;; recursive definition.

(defun restricted-formulap (f v-list)
  (cond ((atom f) (or (ltl-constantp f) 
                      (and (ltl-variablep f)
                           (memberp f v-list))))
        ((equal (len f) 3) (and (memberp (second f) '(& + U W))
                                (restricted-formulap (first f) v-list)
                                (restricted-formulap (third f) v-list)))
        ((equal (len f) 2) (and (memberp (first f) '(~ X F G))
                                (restricted-formulap (second f) v-list)))
        (t nil)))

;; Now we show the obvious thing that a restricted formula is also an ltl
;; formula.

(defthm restricted-formula-is-an-ltl-formula
  (implies (restricted-formulap f v-list)
           (ltl-formulap f))
  :rule-classes :forward-chaining)

;; Given an LTL formula, can we create a v-list such that the LTL-formula is a
;; restricted formula over the variables in v-list? The function
;; create-restricted-var-set attempts that.

(defun create-restricted-var-set (f)
  (cond ((atom f) (if (ltl-constantp f) nil (list f)))
        ((equal (len f) 3) (set-union (create-restricted-var-set (first f))
                                      (create-restricted-var-set (third f))))
        ((equal (len f) 2) (create-restricted-var-set (second f)))
        (t nil)))  

;; And show that we have been successful

(local
(defthm restricted-formulap-append-reduction
  (implies (restricted-formulap f vars)
           (restricted-formulap f (set-union vars vars-prime)))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(local
(defthm restricted-formulap-append-reduction-2
  (implies (restricted-formulap f vars)
           (restricted-formulap f (set-union vars-prime vars)))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(defthm ltl-formula-is-a-restricted-formula
  (implies (ltl-formulap f)
           (restricted-formulap f (create-restricted-var-set f)))
  :rule-classes :forward-chaining)

;; OK, so we are done with syntax of LTL for mow. We will revisit this section
;; and add different restricted models when we do proofs of different
;; reductions.

;; We turn our attention to models.

;; First this handy collection of functions that might help us. 
;; NOTE TO MYSELF: I should write some utilities in ACL2 that will allow me to
;; load the accessor and updater macros easily. I will have to think about it
;; at aome point.

;; Here are the accessors and updaters as macros. A Kripke structure is a
;; record of states, initial-states, transition and label-fn.

(defmacro initial-states (m) `(<- ,m :initial-states))  
(defmacro transition     (m) `(<- ,m :transition))
(defmacro label-fn       (m) `(<- ,m :label-fn))
(defmacro states         (m) `(<- ,m :states))
(defmacro variables      (m) `(<- ,m :variables))

;; A periodic path is a record of initial-state, (finite) prefix, and (finite)
;; cycle.

;; NOTE TO MYSELF: The initial state might not be required. It is difficult to
;; estimate what is considered standard for Kripke structures. I have heard
;; Professor Emerson talk about Kripke Structures with initial states and
;; Kripke Structures without initial states (and so in Dr. Clarke's Book). I
;; follow the "with initial states" in that jargon, though I do believe that we
;; can modify the theorems for Kripke Structures "without initial states". The
;; reason for this choice is that I think the stronger requirements of "without
;; initial states" should not bother us at this time.

(defmacro initial-state  (p) `(<- ,p :initial-state))
(defmacro cycle          (p) `(<- ,p :cycle))
(defmacro prefix         (p) `(<- ,p :prefix))

(defmacro >_ (&rest upds) `(update nil ,@upds)) 

(defun next-statep (p q m)
  (memberp q (<- (transition m) p)))

(defun initial-statep (p m)
  (memberp p (initial-states m)))

(defun label-of (s m)
  (<- (label-fn m) s))

(in-theory (disable next-statep initial-statep label-of))

;; The predicate modelp here precisely describes what we expect a Kripke
;; Structure to look like. 

(defun next-states-in-states (m states)
  (if (endp states) T
    (and (subset (<- (transition m) (first states))
                 (states m))
         (next-states-in-states m (rest states)))))

(defthm next-states-in-states-clarified-aux
  (implies (and (memberp p states)
                (next-states-in-states m states)
                (next-statep p q m))
           (memberp q (states m)))
  :hints (("Goal"
           :in-theory (enable next-statep))))

(defthm next-states-in-states-clarified
  (implies (and (next-states-in-states m (states m))
                (memberp p (states m))
                (next-statep p q m))
           (memberp q (states m))))

(in-theory (disable next-states-in-states-clarified-aux
                    next-states-in-states))

