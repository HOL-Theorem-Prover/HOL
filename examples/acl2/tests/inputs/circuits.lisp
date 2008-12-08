(in-package "ACL2")

#|

  circuits.lisp
  ~~~~~~~~~~~~~

In this book, we discuss a procedure to construct Kripke Structures from
"circuit descriptions. A circuit in our world is a collection of variables, a
collection of equations, and a collection of equations. An equation is a
boolean evaluator of the current circuit valuaes producing the next state
function. We show that under certain "well-formed-ness constraints", our
procedure produces a valid model, in terms of the circuit-modelp predicate
defined earlier.

|#


(include-book "circuit-bisim")


;; A circuit is a collection of variables, equations and initial states. We
;; will add equations to the macros, and tell you what is a good circuit.

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


;; Since I have defined the Kripke model for a circuit, let us prove that it is
;; a circuit-model-p. 

;; We start with the initial states.

;; The theorem that initial-states are subsets of states is trivial by
;; union. So there is nothing to prove.

(local
(defthm initial-states-are-subset-of-states
  (subset (initial-states (create-kripke C)) (states (create-kripke C))))
)

;; END of proofs on initial-states.

;; OK, let us prove that create-label-fn is a valid label function.

(local
(defthm label-fn-is-subset
  (subset (label-fn-of-st st vars) vars))
)

(local
(defthm label-fn-of-st-is-truth-p-label
  (truthp-label (label-fn-of-st st vars) st))
)

(local
(defthm label-fn-of-st-is-all-truths-p-label
  (all-truthsp-label (label-fn-of-st st vars) st vars))
)

(local
(defun abs-only-all-truths-p (states label vars)
  (if (endp states) T
    (and (all-truthsp-label (<- label (first states)) (first states) vars)
         (abs-only-all-truths-p (rest states) label vars))))
)

(local
(defthm abs-concrete-only-all-truthsp-reduction
  (equal (only-all-truths-p states m vars)
         (abs-only-all-truths-p states (label-fn m) vars))
  :hints (("Goal"
           :in-theory (enable label-of))))
)

;; And now let us just prove abs-all-truthsp-label for the label-fn


(local
(defthm create-label-fn-does-not-mess-with-non-members
  (implies (not (memberp s states))
           (equal (<- (create-label-fn states vars label) s)
                  (<- label s))))
)

(local
(defthm create-label-fn-creates-an-all-truthsp-label
  (implies (memberp s states)
           (equal (<- (create-label-fn states vars label) s)
                  (label-fn-of-st s vars))))
)

(local
(defthm label-fn-is-abs-only--all-truthsp
  (abs-only-all-truths-p states (create-label-fn states vars label) vars)
  :hints (("Subgoal *1/3"
           :cases ((memberp (car states) (cdr states)))
           :do-not-induct t)))
)

(local
(defthm label-fn-is-only-all-truthsp
  (only-all-truths-p (states (create-kripke C)) (create-kripke C) 
                     (variables C)))
)

(local
(in-theory (disable abs-concrete-only-all-truthsp-reduction))
)

(local
(defun abs-label-subset-vars (states label vars)
  (if (endp states) T
    (and (subset (<- label (first states)) vars)
         (abs-label-subset-vars (rest states) label vars))))
)

(local
(defthm abs-label-subset-vars-is-same-as-concrete
  (equal (label-subset-vars states m vars)
         (abs-label-subset-vars states (label-fn m) vars))
  :hints (("Goal"
           :in-theory (enable label-of))))
)

(local
(defthm create-label-fn-is-abs-label-subset-vars
  (abs-label-subset-vars states (create-label-fn states vars label) vars)
  :hints (("Subgoal *1/3"
          :cases ((memberp (car states) (cdr states)))
          :do-not-induct t)))
)

(local
(defthm label-fn-is-label-subset-vars
  (label-subset-vars (states (create-kripke C)) (create-kripke C) (variables
                                                                   C)))
)

(local
(in-theory (disable abs-label-subset-vars-is-same-as-concrete))
)

(local
(defun abs-only-truth-p (states label)
  (if (endp states) T
    (and (truthp-label (<- label (first states)) (first states))
         (abs-only-truth-p (rest states) label))))
)

(local
(defthm only-truth-p-abs-reduction
  (equal (only-truth-p states m)
         (abs-only-truth-p states (label-fn m)))
  :hints (("Goal"
           :in-theory (enable label-of))))
)

(local
(defthm label-fn-is-abs-only-truth-p
  (abs-only-truth-p states (create-label-fn states vars label))
  :hints (("Subgoal *1/3"
           :cases ((memberp (car states) (cdr states))))))
)

(local
(defthm label-fn-is-only-truth-p
  (only-truth-p (states (create-kripke C)) (create-kripke C)))
)

(local
(in-theory (disable only-truth-p-abs-reduction))
)

;; END of proofs for label function.

;; Let us now work with the transition function.

(local
(defthm create-next-states-is-subset-of-states-aux
  (implies (memberp q (create-next-states-of-p p states vars equations))
           (memberp q states)))
)

(local
(defthm create-next-states-of-p-subset-helper
  (implies (subset states-prime (create-next-states-of-p p states vars
                                                         equations))
           (subset states-prime states)))
)


(local
(defthm create-next-states-is-subset-of-states
  (subset (create-next-states-of-p p states vars equations)
          states)
  :hints (("Goal"
           :use ((:instance create-next-states-of-p-subset-helper
                            (states-prime (create-next-states-of-p p states
                                                                   vars equations)))))))
)

(local
(defthm not-memberp-next-states-reduction
  (implies (not (memberp s states))
           (equal (<- (create-next-states states states-prime vars equations)
                      s)
                  nil)))
)

(local
(defthm memberp-next-state-reduction
  (implies (memberp s states)
           (equal (<- (create-next-states states states-prime vars equations) 
                      s)
                  (create-next-states-of-p s states-prime vars equations)))
  :hints (("Subgoal *1/3"
           :cases ((equal s (car states))))))
)

(local
(defthm transition-subset-p-for-next-state
  (transition-subset-p states states-prime 
                       (create-next-states states states-prime vars
                                           equations))
  :otf-flg t
  :hints (("Subgoal *1/2"
           :cases ((memberp (car states) (cdr states)))))))

(local
(defthm transition-subset-p-holds-for-kripke
  (transition-subset-p (states (create-kripke C))
                       (states (create-kripke C))
                       (transition (create-kripke C))))
)

(local
(defthm next-states-in-states-concretized
  (equal (next-states-in-states m states)
         (transition-subset-p states (states m) (transition m)))
  :hints (("Goal"
           :in-theory (enable next-states-in-states))))
)

(local
(defthm next-states-in-states-holds-for-create-kripke
  (next-states-in-states (create-kripke C) (states (create-kripke C))))
)


;; END of proofs for transition function.

;; BEGIN proofs for states

;; first states is a consp

(local
(defthm consp-states-for-consp-vars
  (implies (consp states)
           (consp (create-all-evaluations vars states))))
)

;; The following theorem is a hack. This theorem is known as a
;; type-prescription rule for append. Unfortunately, we need it as a rewrite
;; rule.

(local
(in-theory (enable set-union))
)

(local
(defthm consp-union-reduction
  (implies (consp y)
           (consp (set-union x y))))
)

(local
(defthm create-kripke-is-consp-states
  (consp (states (create-kripke C))))
)

;; OK let us prove that everything is boolean with create-all-evaluations

(local
(defthm only-evaluations-p-union-reduction
  (implies (and (only-evaluations-p init vars)
                (only-evaluations-p states vars))
           (only-evaluations-p (set-union init states) vars)))
)

;; OK that takes care of the set-union part. Now we only need to show the
;; create-all-evaluations produces only-evaluations-p

(local
(defun boolean-p-states (v states)
  (if (endp states) T
    (and (booleanp (<- (first states) v))
         (boolean-p-states v (rest states)))))
)

(local
(defun boolean-list-p-states (vars states)
  (if (endp vars) T
    (and (boolean-p-states (first vars) states)
         (boolean-list-p-states (rest vars) states))))
)

;; Now can we prove that boolean-p-states holds for create-all-evaluations?

(local
(defthm assign-t-produces-boolean-p
  (boolean-p-states v (assign-T v states)))
)

(local
(defthm assign-nil-produces-boolean-p
  (boolean-p-states v (assign-nil v states)))
)

(local
(defthm assign-T-remains-same-for-not-v
  (implies (not (equal v v-prime))
           (equal (boolean-p-states v (assign-T v-prime states))
                  (boolean-p-states v states))))
)

(local
(defthm assign-nil-remains-same-for-not-v
  (implies (not (equal v v-prime))
           (equal (boolean-p-states v (assign-nil v-prime states))
                  (boolean-p-states v states))))
)

(local
(defthm boolean-p-append-reduction
  (equal (boolean-p-states v (append states states-prime))
         (and (boolean-p-states v states)
              (boolean-p-states v states-prime))))
)

(local
(defthm boolean-p-create-non-member-reduction
  (implies (not (memberp v vars))
           (equal (boolean-p-states v (create-all-evaluations vars states))
                  (boolean-p-states v states)))
  :hints (("Goal"
           :induct (create-all-evaluations vars states)
           :do-not-induct t)))
)

(local
(defthm create-all-evaluations-for-member-is-boolean
  (implies (memberp v vars)
           (boolean-p-states v (create-all-evaluations vars states)))
  :hints (("Goal"
           :induct (create-all-evaluations vars states)
           :do-not-induct t)
          ("Subgoal *1/2"
           :cases ((equal v (car vars))))))
)

(local
(defthm create-all-evaluations-is-boolean-list-p-aux
  (implies (subset vars vars-prime)
           (boolean-list-p-states vars 
                                  (create-all-evaluations vars-prime states))))
)

(local
(defthm create-all-evaluations-is-boolean-list-p
  (boolean-list-p-states vars (create-all-evaluations vars states)))
)

;; Can we prove that if we produce a boolean list then it is an evaluation?

(local
(defun evaluation-witness-variable (vars st)
  (if (endp vars) nil
    (if (not (booleanp (<- st (first vars))))
        (first vars)
      (evaluation-witness-variable (rest vars) st))))
)

(local
(defthm evaluation-p-from-witness
  (implies (booleanp (<- st (evaluation-witness-variable vars st)))
           (evaluation-p st vars)))
)

(local
(defthm boolean-list-p-to-boolean-vars
  (implies (and (boolean-list-p-states vars states)
                (memberp v vars))
           (boolean-p-states v states)))
)

(local
(defthm boolean-p-states-implies-boolean-v
  (implies (and (boolean-p-states v states)
                (memberp st states))
           (booleanp (<- st v))))
)

(local
(defthm boolean-p-states-to-evaluation-p
  (implies (and (boolean-list-p-states vars states)
                (memberp st states))
           (evaluation-p st vars)))
)

(local
(defthm boolean-p-states-to-only-evaluation-p-aux
  (implies (and (boolean-list-p-states vars states)
                (subset states-prime states))
           (only-evaluations-p states-prime vars)))
)

(local
(defthm boolean-p-states-to-only-evaluations-p
  (implies (boolean-list-p-states vars states)
           (only-evaluations-p states vars)))
)

(local
(defthm create-all-evaluations-is-only-evaluations-p
  (only-evaluations-p (create-all-evaluations vars states) vars))
)

(local
(defthm create-kripke-is-only-evaluations-p
  (implies (circuitp C)
           (only-evaluations-p (states (create-kripke C)) (variables C))))
)

;; The final predicate is all-evaluations-p. This is tricky, since it is
;; defined using defun-sk. We try to create a witness for all-evaluations-p.

(local
(defun find-matching-states (st vars states)
  (cond ((endp vars) states)
        ((equal (<- st (first vars)) T)
         (assign-t (first vars) 
                   (find-matching-states st (rest vars) states)))
        (t (assign-nil (first vars)
                       (find-matching-states st (rest vars) states)))))
)

;; Let us first prove find-matching-states is a consp

(local
(defthm find-matching-states-is-consp
  (implies (consp states)
           (consp (find-matching-states st vars states))))
)

;; Now let us prove that for every member of find-matching-states it is
;; evaluation-eq to st.

(local
(defthm nth-member-reduction
  (implies (and (< i (len x))
                (consp x))
           (memberp (nth i x) x)))
)

(local
(defthm nth-member-reduction-2
  (implies (and (>= i (len x))
                (integerp i))
           (equal (nth i x) nil))
  :hints (("Goal"
           :in-theory (enable zp))))
)

(local
(defthm assign-nil-produces-nil-member
  (implies (memberp q (assign-nil v states))
           (equal (<- q v) nil)))
)

(local
(defthm assign-t-produces-t-member
  (implies (memberp q (assign-t v states))
           (equal (<- q v) t)))
)

(local
(defthm assign-nil-produces-nil
  (implies (and (consp states)
                (integerp i))
           (not (<- (nth i (assign-nil v states)) v)))
  :otf-flg t
  :hints (("Goal"
           :cases ((>= i (len (assign-nil v states))))
           :do-not-induct t)
          ("Subgoal 2"
           :in-theory (disable nth-member-reduction)
           :use ((:instance nth-member-reduction
                            (x (assign-nil v states)))))))
)

(local
(defthm assign-t-has-same-len
  (equal (len (assign-t v states))
         (len states)))
)

(local
(defthm assign-nil-has-same-len
  (equal (len (assign-nil v states))
         (len states)))
)

(local
(defthm len-consp-reduction
  (implies (and (equal (len x) (len y))
                (consp x))
           (consp y)))
)

(local
(defthm assign-t-produces-t
  (implies (and (consp states)
                (< i (len states))
                (integerp i))
           (equal (<- (nth i (assign-t v states)) v) t))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable nth-member-reduction)
           :use ((:instance nth-member-reduction
                            (x (assign-t v states)))))))
)

(local
(defthm assign-t-does-not-fuss
  (implies (and (consp states)
                (< i (len states))
                (integerp i)
                (not (equal v v-prime)))
           (equal (<- (nth i (assign-t v states)) v-prime)
                  (<- (nth i states) v-prime))))
)

(local
(defthm assign-nil-does-not-fuss
  (implies (and (consp states)
                (< i (len states))
                (integerp i)
                (not (equal v v-prime)))
           (equal (<- (nth i (assign-nil v states)) v-prime)
                  (<- (nth i states) v-prime))))
)

(local
(defthm len-of-find-matching-states-is-same
  (equal (len (find-matching-states st vars states))
         (len states)))
)

(local
(defthm find-matching-state-produces-equivalent-assignment
  (implies (and (memberp v vars)
                (consp states)
                (integerp i)
                (< i (len states))
                (evaluation-p st vars))
           (equal (<- (nth i (find-matching-states st vars states)) v)
                  (<- st v)))
  :otf-flg t
  :hints (("Goal"
           :induct (find-matching-states st vars states)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)
          ("Subgoal *1/3.1"
           :cases ((equal v (car vars))))
          ("Subgoal *1/2.1"
           :cases ((equal v (car vars))))))
)

(local
(defun falsifier-evaluation-eq (p q vars)
  (if (endp vars) nil
    (if (not (equal (<- p (first vars))
                    (<- q (first vars))))
        (first vars)
      (falsifier-evaluation-eq p q (rest vars)))))
)

(local
(defthm falsifier-means-evaluation-eq
  (implies (equal (<- p (falsifier-evaluation-eq p q vars))
                  (<- q (falsifier-evaluation-eq p q vars)))
           (evaluation-eq p q vars)))
)

(local
(defthm falsifier-not-member-to-evaluation-eq
  (implies (not (memberp (falsifier-evaluation-eq p q vars) vars))
           (evaluation-eq p q vars)))
)

(local
(defthm find-matching-states-evaluation-eq
  (implies (and (consp states)
                (integerp i)
                (< i (len states))
                (evaluation-p st vars))
           (evaluation-eq (nth i (find-matching-states st vars states))
                          st vars))
  :hints (("Goal"
           :cases ((not (memberp 
                         (falsifier-evaluation-eq 
                          (nth i (find-matching-states st vars states))
                          st vars)
                         vars))))))
)

(local
 (defthm len-not-consp
   (implies (equal (len x) 0)
            (not (consp x)))
   :rule-classes :forward-chaining))

(local
(defthm find-matching-is-evaluation-eq-concretized
  (implies (and (consp states)
                (evaluation-p st vars))
           (evaluation-eq (car (find-matching-states st vars states))
                          st vars))
  :hints (("Goal"
           :in-theory (disable find-matching-states-evaluation-eq)
           :use ((:instance find-matching-states-evaluation-eq
                            (i 0))))))
)

(local
(defthm memberp-append-reduction
  (equal (memberp a (append x y))
         (or (memberp a x)
             (memberp a y))))
)

(local
(defthm member-assign-t-reduction
  (implies (memberp e x)
           (memberp (-> e v t)
                    (assign-t v x))))
)

(local
(defthm assign-t-subset-reduction
  (implies (subset x y)
           (subset (assign-t v x) 
                   (assign-t v y))))
)

(local
(defthm member-assign-nil-reduction
  (implies (memberp e x)
           (memberp (-> e v nil)
                    (assign-nil v x))))
)

(local
(defthm assign-nil-subset-reduction
  (implies (subset x y)
           (subset (assign-nil v x) 
                   (assign-nil v y))))
)

(local
(defthm append-subset-reduction-1
  (implies (subset x y)
           (subset x (append y z))))
)

(local
(defthm append-subset-reduction-2
  (implies (subset x y)
           (subset x (append z y))))
)

(local
(defthm find-matching-subset-reduction
  (subset (find-matching-states st vars states)
          (create-all-evaluations vars states)))
)

(local
(defthm car-of-find-matching-is-member-of-all-evaluations
  (implies (consp states)
           (memberp (car (find-matching-states st vars states))
                    (create-all-evaluations vars states))))
)

(local
(defthm evaluation-eq-memberp-from-memberp
  (implies (and (evaluation-eq p q vars)
                (memberp q states))
           (evaluation-eq-member-p p states vars)))
)

(local
(defthm evalaution-eq-symmetry-hack
  (implies (and (evaluation-eq p q vars)
                (memberp p states))
           (evaluation-eq-member-p q states vars))
  :hints (("Goal"
           :in-theory (disable evaluation-eq evaluation-eq-member-p
                               evaluation-eq-memberp-from-memberp)
           :use ((:instance evaluation-eq-memberp-from-memberp
                            (p q)
                            (q p))
                 (:instance evaluation-eq-is-symmetric)))))
)

(local
(in-theory (disable evaluation-eq-memberp-from-memberp))
)

(local
(defthm create-all-evaluations-is-evaluation-eq-memberp
  (implies (and (evaluation-p st vars)
                (consp states))
           (evaluation-eq-member-p st (create-all-evaluations vars states)
                                   vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable evalaution-eq-symmetry-hack)
           :use ((:instance evalaution-eq-symmetry-hack
                            (q st)
                            (states (create-all-evaluations vars states))
                            (p (car (find-matching-states st vars
                                                          states))))))))
)

(local
(defthm consp-states-to-all-evaluations-p
  (implies (consp states)
           (all-evaluations-p (create-all-evaluations vars states) vars))
  :hints (("Goal"
           :use ((:instance (:definition all-evaluations-p)
                            (states (create-all-evaluations vars states)))))))
)

(local
(defthm append-evaluation-eq-member-reduction
  (implies (evaluation-eq-member-p st states vars)
           (evaluation-eq-member-p st (set-union init states) vars)))
)

(local
(defthm all-evaluations-p-union-reduction
  (implies (all-evaluations-p states vars)
           (all-evaluations-p (set-union init states) vars))
  :hints (("Goal"
            :use ((:instance all-evaluations-p-necc)
                 (:instance (:definition all-evaluations-p)
                            (states (set-union init states)))))))
)

(local
(defthm create-kripke-is-all-evaluations-p
  (all-evaluations-p (states (create-kripke C))
                     (variables c)))
)

(local
(defthm variables-of-create-kripke-are-original-vars
  (equal (variables (create-kripke C))
         (variables C)))
)

(local
(defthm strict-evaluations-list-to-evaluation
  (implies (and (strict-evaluation-list-p vars states)
                (memberp st states))
           (strict-evaluation-p st vars)))
)

(local
(defthm strict-evaluations-append-reduction
  (implies (and (strict-evaluation-list-p vars states)
                (strict-evaluation-list-p vars states-prime))
           (strict-evaluation-list-p vars (append states states-prime))))
)

(local
(defthm strict-evaluation-list-p-nth-reduction
  (implies (and (strict-evaluation-list-p vars states)
                (integerp i)
                (< i (len states))
                (consp states))
           (strict-evaluation-p (nth i states) vars)))
)

(local
(defthm assign-t-strict-evaluations-reduction
  (implies (and (strict-evaluation-list-p vars states)
                (memberp v vars)
                (consp states)
                (integerp i)
                (< i (len states))
                (not (memberp v-prime vars)))
           (not (<- (nth i (assign-t v states)) v-prime)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable assign-t-does-not-fuss)
           :use ((:instance assign-t-does-not-fuss)
                 (:instance strict-evaluation-p-necc 
                            (v v-prime)
                            (st (nth i states)))))))
)

(local
(defthm assign-nil-strict-evaluations-reduction
  (implies (and (strict-evaluation-list-p vars states)
                (memberp v vars)
                (consp states)
                (integerp i)
                (< i (len states))
                (not (memberp v-prime vars)))
           (not (<- (nth i (assign-nil v states)) v-prime)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable assign-nil-does-not-fuss)
           :use ((:instance assign-nil-does-not-fuss)
                 (:instance strict-evaluation-p-necc 
                            (v v-prime)
                            (st (nth i states)))))))
)

(local
(defthm strict-evaluations-assign-t-reduction
  (implies (and (integerp i)
                (consp states)
                (strict-evaluation-list-p vars states)
                (memberp v vars)
                (< i (len states)))
           (strict-evaluation-p (nth i (assign-t v states)) vars)))
)

(local
(defthm strict-evaluations-assign-nil-reduction
  (implies (and (integerp i)
                (consp states)
                (strict-evaluation-list-p vars states)
                (memberp v vars)
                (< i (len states)))
           (strict-evaluation-p (nth i (assign-nil v states)) vars)))
)

(local
(defun find-index (st states)
  (if (endp states) 0
    (if (equal st (first states)) 0
      (1+ (find-index st (rest states))))))
)

(local
(defthm find-index-is-memberp
  (implies (memberp st states)
           (equal (nth (find-index st states) states)
                  st)))
)

(local
(defthm find-index-returns-<-len
  (implies (memberp st states)
           (< (find-index st states) (len states)))
  :rule-classes :linear)
)

(local
(defthm strict-evaluation-for-memberp-assign-t
  (implies (and (consp states)
                (strict-evaluation-list-p vars states)
                (memberp v vars)
                (memberp st (assign-t v states)))
           (strict-evaluation-p st vars))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable assign-t-strict-evaluations-reduction
                               strict-evaluation-p)
           :use ((:instance strict-evaluations-assign-t-reduction 
                            (i (find-index st (assign-t v states))))))))
)

(local
(defthm strict-evaluation-for-memberp-assign-nil
  (implies (and (consp states)
                (strict-evaluation-list-p vars states)
                (memberp v vars)
                (memberp st (assign-nil v states)))
           (strict-evaluation-p st vars))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable assign-nil-strict-evaluations-reduction
                               strict-evaluation-p)
           :use ((:instance strict-evaluations-assign-nil-reduction 
                            (i (find-index st (assign-nil v states))))))))
)

(local
(in-theory (disable strict-evaluation-p))
)

(local
(defthm strict-evaluations-for-assign-t
  (implies (and (consp states)
                (strict-evaluation-list-p vars states)
                (memberp v vars))
           (strict-evaluation-list-p vars (assign-t v states))))
)

(local
(defthm strict-evaluations-for-assign-nil
  (implies (and (consp states)
                (strict-evaluation-list-p vars states)
                (memberp v vars))
           (strict-evaluation-list-p vars (assign-nil v states))))
)

(local
(defun null-list-p (states)
  (if (endp states) T
    (and (null (first states)) 
         (null-list-p (rest states)))))
)

(local
(defthm strict-evaluation-p-cons-reduction
  (implies (strict-evaluation-p st vars)
           (strict-evaluation-p (-> st v t) (cons v vars)))
  :hints (("Goal"
           :expand (strict-evaluation-p (-> st v t) (cons v vars)))))
)

(local
(defthm strict-evaluation-p-cons-reduction-2
  (implies (strict-evaluation-p st vars)
           (strict-evaluation-p (-> st v nil) (cons v vars)))
  :hints (("Goal"
           :expand (strict-evaluation-p (-> st v nil) (cons v vars)))))
)

(local
(defthm strict-evaluation-p-assign-reduction-t
  (implies (strict-evaluation-list-p vars states)
           (strict-evaluation-list-p (cons v vars) (assign-t v states))))
)

(local
(defthm strict-evaluation-p-assign-reduction-nil
  (implies (strict-evaluation-list-p vars states)
           (strict-evaluation-list-p (cons v vars) (assign-nil v states))))
)

(local
(defthm nil-is-strict-evaluation-p
  (strict-evaluation-p nil vars)
  :hints (("Goal"
           :in-theory (enable strict-evaluation-p))))
)

(local
(defthm null-list-p-is-strict-evaluation-p
  (implies (null-list-p states)
           (strict-evaluation-list-p vars states)))
)

(local
(defthm create-evaluations-is-strict-evaluation-list-p
  (implies (and (consp states)
                (null-list-p states)
                (uniquep vars))
           (strict-evaluation-list-p 
            vars (create-all-evaluations vars states)))
  :otf-flg t
  :hints (("Goal"
           :induct (create-all-evaluations vars states)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)
          ("Subgoal *1/2"
           :in-theory (disable strict-evaluation-p-assign-reduction-t
                               strict-evaluation-p-assign-reduction-nil)
           :use ((:instance strict-evaluation-p-assign-reduction-t
                            (states (create-all-evaluations (cdr vars) states))
                            (vars (cdr vars))
                            (v (car vars)))
                 (:instance strict-evaluation-p-assign-reduction-nil
                            (states (create-all-evaluations (cdr vars) states))
                            (vars (cdr vars))
                            (v (car vars)))))))
)

(local                 
(defthm strict-evaluation-set-union-reduction
  (implies (and (strict-evaluation-list-p vars init)
                (strict-evaluation-list-p vars states))
           (strict-evaluation-list-p vars (set-union init states)))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(local
(defthm strict-evaluation-list-p-holds
  (implies (circuitp C)
           (strict-evaluation-list-p (variables C) (states (create-kripke C)))))
)

(local
(in-theory (disable create-kripke))
)

(DEFTHM create-kripke-produces-circuit-model
  (implies (circuitp C)
           (circuit-modelp (create-kripke C))))
           
