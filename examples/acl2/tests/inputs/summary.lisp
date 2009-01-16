(in-package "ACL2")

#||

  summary.lisp
  ~~~~~~~~~~~~

Author: Sandip Ray
Date: Sat Nov  8 15:27:38 2008

In this book, we summarize the theorems that demonstrate that the
conee of influence reduction of a circuit produces a Kripke Structure
which is bisimilar to the circuit.  I locally include some of the
earlier books by Ray/Matthews/Tuttle to show this.  The book here only
states the theorems previously proven in the above books nonlocally.
These theorems correspond to the "easy part" of showing that cone of
influence reduction preserves LTL semantics.  The hard part, that
bisimulation preserves LTL semantics, should be an easy problem for
HOL.

||#

;; I now locally include the cone of influence book, which has all the
;; proofs.  Here I non-locally state the theorems.
(local (include-book "cone-of-influence"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section 1: Some Preliminaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This records book is similar to what is distributed with ACL2 (I
;; hope).  But this was done in Summer 2002 when all this was in flux.
;; So I used a version of the records book which might be
;; non-standard.  At some point I need to sit and understand how to
;; get everything working with the distributed records book.

(include-book "records")

(defmacro <- (x a) `(g ,a ,x))
(defmacro -> (x a v) `(s ,a ,v ,x))

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))

(defmacro >_ (&rest upds) `(update nil ,@upds)) 

(local (include-book "cone-of-influence"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section 2: Set Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that this work was done in Summer 2002, when there was no good
;; set book that suited my purpose.  So I rolled my own little set of
;; set theorems.  If I were doing it today, I probably would have made
;; use of the distributed set theory books.

(defun memberp (a x)
  (and (consp x)
       (or (equal a (first x))
           (memberp a (rest x)))))

(defun subset (x y)
  (if (endp x) T
    (and (memberp (first x) y)
         (subset (rest x) y))))

(defun set-intersect (x y)
  (cond ((endp x) nil)
        ((memberp (first x) y) 
         (cons (first x) (set-intersect (rest x) y)))
        (t (set-intersect (rest x) y))))

(defun set-union (x y)
  (cond ((endp x) y)
        ((memberp (first x) y)
         (set-union (rest x) y))
        (t (cons (first x) (set-union (rest x) y)))))

(defun set-equal (x y)
  (and (subset x y)
       (subset y x)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section 3: LTL formulas and their structure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Why do I need an LTL formula, if all we are doing is bisimulation
;; proof?  Because the correctness of cone of influence reduction is
;; stated as the following theorem.  Suppose f be an LTL formula, and
;; C a circuit.  Reduce the circuit with the cone of influence of the
;; variables in f.  Then the reduced circuit satisfies f if and only
;; if the original does.

(defun ltl-constantp (f)
  (or (equal f 'true)
      (equal f 'false)))

(defun ltl-variablep (f)
  (and (symbolp f)
       (not (memberp f '(+ & U W X F G)))))

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

;; A formula is called restricted with respect to a collection vars of
;; variables if it mentions no variable other than those in vars. Here
;; is the recursive definition.

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section 4: Kripke Structures from Circuits, and a bisimulation relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro initial-states (m) `(<- ,m :initial-states))  
(defmacro transition     (m) `(<- ,m :transition))
(defmacro label-fn       (m) `(<- ,m :label-fn))
(defmacro states         (m) `(<- ,m :states))
(defmacro variables      (m) `(<- ,m :variables))

(defun next-statep (p q m)
  (memberp q (<- (transition m) p)))

(defun initial-statep (p m)
  (memberp p (initial-states m)))

(defun label-of (s m)
  (<- (label-fn m) s))

(defun next-states-in-states (m states)
  (if (endp states) T
    (and (subset (<- (transition m) (first states))
                 (states m))
         (next-states-in-states m (rest states)))))

(defun evaluation-eq (p q vars)
  (if (endp vars) T
    (and (equal (<- p (first vars))
                (<- q (first vars)))
         (evaluation-eq p q (rest vars)))))

(defun evaluation-eq-member-p (st states vars)
  (if (endp states) nil
    (if (evaluation-eq st (first states) vars) T
      (evaluation-eq-member-p st (rest states) vars))))

(defun evaluation-eq-member (st states vars)
  (if (endp states) nil
    (if (evaluation-eq st (first states) vars)
        (first states)
      (evaluation-eq-member st (rest states) vars))))

(defun-sk strict-evaluation-p (st vars)
  (forall v (implies (not (memberp v vars))
                     (not (<- st v)))))

(defun strict-evaluation-list-p (vars states)
  (if (endp states) T
    (and (strict-evaluation-p (first states) vars)
         (strict-evaluation-list-p vars (rest states)))))

(defun evaluation-p (st vars)
  (if (endp vars) T
    (and (booleanp (<- st (first vars)))
         (evaluation-p st (rest vars)))))

(defun only-evaluations-p (states vars)
  (if (endp states) T
    (and (evaluation-p (first states) vars)
         (only-evaluations-p (rest states) vars))))

;; I think we can remove the all-evaluations-p from defun-sk to
;; defun. But I am feeling lazy at least now to do it.

(defun-sk all-evaluations-p (states vars)
  (forall st
          (implies (evaluation-p st vars)
                   (evaluation-eq-member-p st states vars))))

(defun evaluation-eq-subset-p (m-states n-states vars)
  (if (endp m-states) T
    (and (evaluation-eq-member-p (first m-states) n-states vars)
         (evaluation-eq-subset-p (rest m-states) n-states vars))))

(defthm evaluation-eq-subset-to-member
  (implies (and (evaluation-eq-subset-p m-states n-states vars)
                (memberp p m-states))
           (evaluation-eq-member-p p n-states vars)))

(defun truthp-label (label s)
  (if (endp label) t
    (and (equal (<- s (first label)) T)
         (truthp-label (rest label) s))))
         
(defun only-truth-p (states m)
  (if (endp states) T
    (and (truthp-label (label-of (first states) m) (first states))
         (only-truth-p (rest states) m))))

(defun all-truthsp-label (label s vars)
  (if (endp vars) T
    (and (implies (equal (<- s (car vars)) T)
                  (memberp (car vars) label))
         (all-truthsp-label label s (rest vars)))))

(defun only-all-truths-p (states m vars) 
  (if (endp states) T
    (and (all-truthsp-label (label-of (first states) m) (first states) vars)
         (only-all-truths-p (rest states) m vars))))

(defun label-subset-vars (states m vars)
  (if (endp states) T
    (and (subset (label-of (first states) m) vars)
         (label-subset-vars (rest states) m vars))))

(defun-sk well-formed-transition-p (states-m trans-m states-n trans-n vars)
  (forall (p q)
          (implies (and (evaluation-eq p q vars)
                        (evaluation-p p vars)
                        (memberp p states-m)
                        (memberp q states-n)
                        (evaluation-p q vars))
                   (evaluation-eq-subset-p (<- trans-m p)
                                           (<- trans-n q)
                                           vars))))

(defun transition-subset-p (states states-prime trans)
  (if (endp states) T
    (and (subset (<- trans (first states)) states-prime)
         (transition-subset-p (rest states) states-prime trans))))

(defun circuit-modelp (m)
  (and (only-evaluations-p (states m) (variables m))
       (all-evaluations-p (states m) (variables m))
       (strict-evaluation-list-p (variables m) (states m))
       (only-all-truths-p (states m) m (variables m))
       (only-truth-p (states m) m)
       (label-subset-vars (states m) m (variables m))
       (transition-subset-p (states m) (states m) (transition m))
       (subset (initial-states m) (states m))
       (consp (states m))
       (next-states-in-states m (states m))))

;; And here is our bisimilarity relation

(defun c-bisim-equiv (m n vars)
  (and (circuit-modelp m)
       (circuit-modelp n)
       (subset vars (variables m))
       (subset vars (variables n))
       (well-formed-transition-p (states m) (transition m) (states n) (transition n) vars)
       (well-formed-transition-p (states n) (transition n) (states m) (transition m) vars)
       (evaluation-eq-subset-p (initial-states m) (initial-states n) vars)
       (evaluation-eq-subset-p (initial-states n) (initial-states m) vars)))

(defun circuit-bisim (p m q n vars)
  (and (circuit-modelp m) 
       (circuit-modelp n)
       (memberp p (states m))
       (memberp q (states n))
       (well-formed-transition-p (states m) (transition m) (states n) (transition n) vars)
       (well-formed-transition-p (states n) (transition n) (states m) (transition m) vars)
       (evaluation-eq-subset-p (initial-states m) (initial-states n) vars)
       (evaluation-eq-subset-p (initial-states n) (initial-states m) vars)
       (subset vars (variables m))
       (subset vars (variables n))
       (evaluation-eq p q vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section 5: Circuit Structure and Kripke Structure from Circuit
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro equations (c) `(<- ,c :equations))

;; Now we define what it means for the equations to be consistent with the
;; variables of the circuit.

(defun find-variables (equation)
  (cond ((and (atom equation) (not (booleanp equation)))
         (list equation))
        ((and (equal (len equation) 3) (memberp (second equation) '(& +)))
         (set-union (find-variables (first equation)) 
                    (find-variables (third equation))))
        ((and (equal (len equation) 2) (equal (first equation) '~))
         (find-variables (second equation)))
        (t nil)))

(defun-sk consistent-equation-record-p (vars equations)
  (forall (v equation)
          (implies (and (uniquep vars)
                        (memberp v vars)
                        (memberp equation (<- equations v)))
                   (subset (find-variables equation) vars))))

(defun cons-list-p (vars equations)
  (if (endp vars) T
    (and (consp (<- equations (first vars)))
         (cons-list-p (rest vars) equations))))

;; OK, now let us define the function circuitp.

(defun circuitp (C)
  (and (only-evaluations-p (initial-states C) (variables C))
       (strict-evaluation-list-p (variables C) (initial-states C))
       (uniquep (variables C))
       (cons-list-p (variables C) (equations C))
       (consistent-equation-record-p (variables C) (equations C))))

;; Now let us try to create a Kripke Structure from the circuit. We need to
;; show that under (circuitp C), the kripke structure we produce is a
;; circuit-model-p.

(defun assign-T (v states)
  (if (endp states) nil
    (cons (-> (first states) v T)
          (assign-T v (rest states)))))

(defun assign-nil (v states)
  (if (endp states) nil
    (cons (-> (first states) v nil)
          (assign-nil v (rest states)))))

;; Now we create all the states of the model.

(defun create-all-evaluations (vars states)
  (if (endp vars) states
    (let ((rec-states (create-all-evaluations (cdr vars) states)))
      (append (assign-t (car vars) rec-states)
              (assign-nil (car vars) rec-states)))))

;; Now let us create the label function.

(defun label-fn-of-st (st vars)
  (if (endp vars) nil
    (if (equal (<- st (first vars)) T) 
        (cons (first vars) 
              (label-fn-of-st st (rest vars)))
      (label-fn-of-st st (rest vars)))))

(defun create-label-fn (states vars label)
  (if (endp states) label
    (create-label-fn (rest states) vars
                     (-> label (first states) 
                         (label-fn-of-st (first states) vars)))))

;; And finally the transitions.

(defun apply-equation (equation st)
  (cond ((atom equation) (if (booleanp equation)
                             equation
                           (<- st equation)))
        ((equal (len equation) 2)
         (case (first equation)
           (~ (not (apply-equation (second equation) st)))
           (t nil)))
        ((equal (len equation) 3)
         (case (second equation)
           (& (and (apply-equation (first equation) st)
                   (apply-equation (third equation) st)))
           (+ (or (apply-equation (first equation) st)
                  (apply-equation (third equation) st)))
           (t nil)))
        (t nil)))

(defun produce-next-state (vars st equations)
  (if (endp vars) st
    (-> (produce-next-state (rest vars) st equations)
        (first vars)
        (apply-equation (<- equations (first vars)) st))))

(defun consistent-p-equations (vars eqn equations)
  (if (endp vars) T
    (and (memberp (<- eqn (first vars)) (<- equations (first vars)))
         (consistent-p-equations (rest vars) eqn equations))))

(defun-sk next-state-is-ok (p q vars equations)
  (exists eqn (and (consistent-p-equations vars eqn equations)
                   (evaluation-eq q (produce-next-state vars p eqn) vars))))

(defun create-next-states-of-p (p states vars equations)
  (if (endp states) nil
    (if (next-state-is-ok p (first states) vars equations)
        (cons (first states) (create-next-states-of-p 
                              p (rest states) vars equations))
      (create-next-states-of-p p (rest states) vars equations))))

(defun create-next-states (states states-prime vars equations)
  (if (endp states) ()
    (-> 
     (create-next-states (rest states) states-prime vars equations)
     (first states)
     (create-next-states-of-p (first states) states-prime vars equations))))

(defun create-kripke (C)
  (let ((vars (variables C))
        (equations (equations C))
        (initial-states (initial-states C)))
    (let* ((states (create-all-evaluations vars (list ())))
           (label-fn (create-label-fn (set-union initial-states states) vars ()))
           (transition (create-next-states (set-union initial-states states)
                                           (set-union initial-states states)
                                           vars equations)))
      (>_ :states (set-union initial-states states)
          :initial-states initial-states
          :label-fn label-fn
          :transition transition
          :variables vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section 6: Cone of Influence Reduction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-variables* (equation-list)
  (if (endp equation-list) nil
    (set-union (find-variables (first equation-list))
                      (find-variables* (rest equation-list)))))

(defun find-all-variables-1-pass (vars equations)
  (if (endp vars) nil
    (set-union (find-variables* (<- equations (first vars)))
                      (find-all-variables-1-pass (rest vars) equations))))

(defun find-all-variables (vars variables equations)
  (declare (xargs :measure (nfix (- (len variables) (len vars)))
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (enable set-equal)
                           :do-not '(eliminate-destructors generalize)))))
  (if (or (not (uniquep variables))
          (not (uniquep vars))
          (not (subset vars variables)))
      vars
    (let ((new-vars (set-union (find-all-variables-1-pass vars equations)
                               vars)))
      (if (not (subset new-vars variables)) nil 
        (if (set-equal vars new-vars) vars
          (find-all-variables new-vars variables equations))))))
  
(defun find-all-equations (vars equations eq-rec)
  (if (endp vars) eq-rec
    (find-all-equations (rest vars) equations
                        (-> eq-rec
                            (first vars)
                            (<- equations (first vars))))))
      
(defun remove-duplicate-occurrences (x)
  (cond ((endp x) x)
        ((memberp (first x) (rest x)) (remove-duplicate-occurrences (rest x)))
        (t (cons (first x) (remove-duplicate-occurrences (rest x))))))

(defun corresponding-state (init vars)
  (if (endp vars) nil
    (-> (corresponding-state init (rest vars))
        (first vars)
        (<- init (first vars)))))

(defun corresponding-states (inits vars)
  (if (endp inits) nil
    (cons (corresponding-state (first inits) vars)
          (corresponding-states (rest inits) vars))))

(defun cone-variables (vars C)
  (find-all-variables 
   (set-intersect (remove-duplicate-occurrences vars)
                  (variables C))
   (variables C)
   (equations C)))
                  
(defun cone-of-influence-reduction (C vars)
  (let ((variables (cone-variables vars C)))
   (>_ :variables variables
       :initial-states (corresponding-states (initial-states C) variables)
       :equations (find-all-equations variables (equations C) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section 7: Final Theorems
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We first show that cone of influence reduction produces a circuit,
;; and also that it satisfies the bisimulation relation c-bisim-equiv.

(defthm cone-of-influence-reduction-is-circuit-p
  (implies (circuitp C)
           (circuitp (cone-of-influence-reduction C vars)))
  :hints (("Goal"
           :in-theory (disable circuitp cone-of-influence-reduction)
           :expand (circuitp (cone-of-influence-reduction C vars)))))
                

(defthm cone-of-influence-is-c-bisimi-equiv
  (implies (circuitp C)
           (c-bisim-equiv (create-kripke C)
                           (create-kripke (cone-of-influence-reduction C vars))
                           (cone-variables vars C))))


;; We then show that the Kripke Structure produced from a circuit is
;; indeed a Kripke Structure.

(defthm create-kripke-produces-circuit-model
  (implies (circuitp C)
           (circuit-modelp (create-kripke C))))

;; Now we will show that c-bisim-equiv is indeed a bisimulation
;; relation over Kripke Structures.  This probably does not require
;; that we have a Kripke Structure in our hands.  But what the heck,
;; we have proven this above.  The next few theorems are
;; (non-closed-form) characterization of bisimulation.  When proving
;; that bisimulation preserves LTL semantics we had proven that if
;; there is _any_ bisimulation relation between two Kripke Sturctures,
;; then they preserve the LTL semantics.

;; Bisimulation requires an existential quantification in several
;; spots.  For example, we have to say that for each initial state in
;; m there is an initial state in n, that is bisim-equiv.  Instead of
;; quantifying, we create such a state (for m to n) and (n to m).

(defun c-bisimilar-initial-state-witness-m->n (s m n vars)
  (declare (ignore m))
  (evaluation-eq-member s (initial-states n) vars))

(defun c-bisimilar-initial-state-witness-n->m (m s n vars)
  (declare (ignore n))
  (evaluation-eq-member s (initial-states m) vars))

(defun c-bisimilar-transition-witness-m->n (p r m q n vars)
  (declare (ignore p m))
  (evaluation-eq-member r (<- (transition n) q) vars))

(defun c-bisimilar-transition-witness-n->m (p m q r n vars)
  (declare (ignore q n))
  (evaluation-eq-member r (<- (transition m) p) vars))

;; Now we can state the theorems.

(defthm c-bisimilar-equiv-implies-init->init-m->n
  (implies (and (c-bisim-equiv m n vars)
                (memberp s (initial-states m)))
           (memberp (c-bisimilar-initial-state-witness-m->n s m n vars)
                    (initial-states n))))

(defthm c-bisimilar-equiv-implies-init->init-n->m
  (implies (and (c-bisim-equiv m n vars)
                (memberp s (initial-states n)))
           (memberp (c-bisimilar-initial-state-witness-n->m m s n vars)
                    (initial-states m))))

(defthm c-bisimilar-equiv-implies-bisimilar-initial-states-m->n
   (implies (and (c-bisim-equiv m n vars)
                 (memberp s (initial-states m)))
            (circuit-bisim s m 
                           (c-bisimilar-initial-state-witness-m->n s m n vars) 
                           n vars)))

(defthm c-bisimilar-equiv-implies-bisimilar-initial-states-n->m
   (implies (and (c-bisim-equiv m n vars)
                 (memberp s (initial-states n)))
            (circuit-bisim (c-bisimilar-initial-state-witness-n->m m s n vars) 
                           m s n vars)))

(defthm c-bisimilar-states-have-labels-equal
  (implies (circuit-bisim p m q n vars)
           (set-equal (set-intersect (label-of q n) vars)
                      (set-intersect (label-of p m) vars))))


(defthm c-bisimilar-witness-member-of-states-m->n
  (implies (and (circuit-bisim p m q n vars)
                (next-statep p r m)
                (memberp r (states m)))
           (memberp (c-bisimilar-transition-witness-m->n p r m q n vars)
                    (states n))))

(defthm c-bisimilar-witness-member-of-states-n->m
  (implies (and (circuit-bisim p m q n vars)
                (next-statep q r n)
                (memberp r (states n)))
           (memberp (c-bisimilar-transition-witness-n->m p m q r n vars)
                    (states m))))

(defthm c-bisimilar-witness-produces-bisimilar-states-m->n
  (implies (and (circuit-bisim p m q n vars)
                 (next-statep p r m))
            (circuit-bisim r m
                       (c-bisimilar-transition-witness-m->n p r m q n vars)
                       n vars)))

(defthm c-bisimilar-witness-produces-bisimilar-states-n->m
  (implies (and (circuit-bisim p m q n vars)
                 (next-statep q r n))
            (circuit-bisim 
             (c-bisimilar-transition-witness-n->m p m q r n vars)
             m r n vars)))

(defthm c-bisimilar-witness-matches-transition-m->n
  (implies (and (circuit-bisim p m q n vars)
                (next-statep p r m))
           (next-statep q (c-bisimilar-transition-witness-m->n p r m q n vars)
                        n)))

(defthm c-bisimilar-witness-matches-transition-n->m
  (implies (and (circuit-bisim p m q n vars)
                (next-statep q r n))
           (next-statep p (c-bisimilar-transition-witness-n->m p m q r n vars)
                        m)))
