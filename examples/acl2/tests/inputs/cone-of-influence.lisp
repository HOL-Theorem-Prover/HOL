(in-package "ACL2")

;; The following two lines are added for portability to v2-7....


#|

  cone-of-influence.lisp
  ~~~~~~~~~~~~~~~~~~~~~~

We implement a cone of influence reduction algorithm. Cone of influence is
(roughly) elimination of redundant variables. Given a collection of V variables,
we determine the closure V*, V =< V* =< (variables C) and a collection
E =< (equations C), such that for every variable in V*, the equation in E for
that variable corresponds to the equation in (equations C). We then claim that
the Kripke structure created from the cone-of-influence reduced circuit is
bisimilar with respect to V* to the Kripke Structure created from the original
circuit.

|#


(include-book "circuits") 

;; Here are the two culprit rules that I need to disable to get the proof
;; faster. Just shows how naive a user I was when I did this proof. 

(in-theory (disable subset-of-nil-is-nil
                    subset-of-empty-is-empty))

(defun find-variables* (equation-list)
  (if (endp equation-list) nil
    (set-union (find-variables (first equation-list))
                      (find-variables* (rest equation-list)))))

(defun find-all-variables-1-pass (vars equations)
  (if (endp vars) nil
    (set-union (find-variables* (<- equations (first vars)))
                      (find-all-variables-1-pass (rest vars) equations))))

;; The following function find-all-variables is a difficult function to
;; admit. It computes the closure of a given set of variables (vars) with
;; respect to a collection of variables (variables) and a collection of
;; equations.

(local
(in-theory (enable set-union))
)

(local
(defthm len-set-union-more-than-y
  (<= (len y)
      (len (set-union x y)))
  :rule-classes :linear)
)

(local
(defthm uniquep-member-reduction
  (equal (memberp e (set-union x y))
         (or (memberp e x)
             (memberp e y))))
)

(local
(defthm uniquep-union-reduction
  (implies (and (uniquep x)
                (uniquep y))
           (uniquep (set-union x y))))
)

(local
(defthm find-variables-is-unique
  (uniquep (find-variables equations)))
)

(local
(defthm find-variables*-is-unique
  (uniquep (find-variables* equations)))
)

(local
(defthm find-all-variables-1-pass-is-unique
  (uniquep (find-all-variables-1-pass vars equations)))
)

(defun del (e x)
  (if (endp x) x
    (if (equal e (first x))
        (rest x)
      (cons (first x) (del e (rest x))))))

(local
(defthm len-del-reduction-1
  (implies (memberp e x)
           (equal (len (del e x))
                  (1- (len x))))
  :hints (("Goal"
           :in-theory (enable len))))
)

(defun induction-hint-for-len-<= (x y)
  (if (endp x) (list x y)
    (induction-hint-for-len-<= (cdr x) (del (car x) y))))

(local
(defthm del-not-member-reduction
  (implies (not (memberp e x))
           (equal (del e x) x)))
)

(local
(defthm member-del-reduction
  (implies (not (equal v e))
           (equal (memberp v (del e y))
                  (memberp v y))))
)

(local
(defthm subset-del-member
  (implies (and (not (memberp e x))
                (subset x y))
           (subset x (del e y))))
)

(local
(defthm uniquep-del-reduction
  (implies (uniquep x)
           (uniquep (del e x))))
)

(local
(defthm uniquep-and-subset-implies-len-<=
  (implies (and (uniquep x)
                (uniquep y)
                (subset x y))
           (<= (len x)
               (len y)))
  :hints (("Goal"
           :induct (induction-hint-for-len-<= x y)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm subset-from-union
  (implies (and (subset x z)
                (subset y z))
           (subset (set-union x y) z)))
)

(local
(defthm subset-from-union-2
  (implies (and (subset (set-union x y) z)
                (uniquep x)
                (uniquep y))
           (and (subset x z)
                (subset y z))))
)

(local
(include-book  "arithmetic-2/meta/top" :dir :system)
)

(local
(defthm del-e-to-cons-subset
  (implies (subset (del e y) x)
           (subset y (cons e x))))     
)


(local
 (defthm len-not-consp
   (implies (equal (len x) 0)
            (not (consp x)))
   :rule-classes :forward-chaining))


(local
(defthm len-equal-to-set-equal
  (implies (and (equal (len x) (len y))
                (uniquep x)
                (uniquep y)
                (subset x y))
           (subset y x))
  :hints (("Goal"
           :induct  (induction-hint-for-len-<= x y)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)
          ("Subgoal *1/2.1"
           :in-theory (disable del-e-to-cons-subset)
           :use ((:instance del-e-to-cons-subset
                            (e (car x))
                            (x (cdr x)))))))
)

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

;; OK, so we have implemented the cone of influence reduction. Let us prove
;;that create-kripke of this reduced model is bisim-equiv to create-Kripke of
;; C.

;; Notice that for the bisimilarity proof to go through, the variables that we
;; choose are the variables in the cone. So proving that the variables are subset
;; of the variables of cone is trivial. On the other hand, we need to prove that
;; the variables are subset of the original collection of variables.

(local
(defthm find-all-variables-subset-of-variables
  (implies (and (uniquep vars)
                (uniquep variables)
                (subset vars variables))
  (subset (find-all-variables vars variables equations) variables))
  :hints (("Goal"
           :in-theory (disable subset-of-nil-is-nil
                               subset-of-empty-is-empty))))
)

;; OK, so we know find-all-variables-is-a-subset. We need to prove that vars is
;; a subset and uniquep, though. Now, vars is really remove-duplicates of
;; (set-intersect (remove-duplicates vars) (variables C))

(local
(defthm member-remove-duplicate-reduction
  (equal (memberp e (remove-duplicate-occurrences x))
         (memberp e x)))
)

(local
(defthm unique-duplicate-reduction
  (uniquep (remove-duplicate-occurrences x)))
)

(local
(defthm uniquep-intersect-reduction
  (implies (and (uniquep x)
                (uniquep y))
           (uniquep (set-intersect x y))))
)

(local
(defthm find-all-variables-is-unique
  (implies (uniquep vars)
           (uniquep (find-all-variables vars variables equations)))
  :hints (("Goal"
           :in-theory (disable subset-of-empty-is-empty))))
)

(local
(defthm subset-remove-reduction
  (equal (subset (remove-duplicate-occurrences x) y)
         (subset x y)))
)

(local
(defthm subset-set-intersect-reduction
  (equal (subset (set-intersect (remove-duplicate-occurrences x) y) z)
         (subset (set-intersect x y) z))
  :hints (("Goal"
           :in-theory (disable subset-of-empty-is-empty))))
)

;; And now check that we have done the trick.

(local
(defthm variables-are-subset-of-original
  (implies (circuitp C)
           (subset (cone-variables vars C)
                   (variables (create-kripke C))))
  :hints (("Goal"
           :in-theory (disable subset-of-nil-is-nil
                               subset-of-empty-is-empty)
           :do-not-induct t)))
)

(local
(defthm variables-are-subset-of-cone
  (subset (cone-variables vars C)
          (variables (create-kripke 
                      (cone-of-influence-reduction C vars))))
  :hints (("Goal"
           :in-theory (disable cone-variables))))
)

;; OK, so we have proved that the vars are subset of variables. Let us now work
;; on the initial states.

(local
(defthm evaluation-eq-subset-reduction
  (implies (and (subset vars-prime vars)
                (evaluation-eq p q vars))
           (evaluation-eq p q vars-prime)))
)

(local
(defthm evaluation-eq-member-subset-reduction
  (implies (and (evaluation-eq-member-p init inits vars)
                (subset vars-prime vars))
           (evaluation-eq-member-p init inits vars-prime)))
)

(local
(defthm evaluation-eq-subset-subset-reduction
  (implies (and (evaluation-eq-subset-p inits states vars)
                (subset vars-prime vars))
           (evaluation-eq-subset-p inits states vars-prime)))
)

(local
(defthm corresponding-states-are-evaluation-eq
  (implies (uniquep vars)
           (evaluation-eq init (corresponding-state init vars)  vars)))
)

(local
(defthm corresponding-state-is-member-of-corresponding-states
  (implies (memberp init inits)
           (memberp (corresponding-state init vars)
                    (corresponding-states inits vars))))
)

(local
(defthm evaluation-eq-memberp-of-corresponding-states
  (implies (and (uniquep vars)
                (memberp init inits))
           (evaluation-eq-member-p init (corresponding-states inits vars)
                                   vars)))
)

(local
(defthm evaluation-eq-subsets-reduction
  (implies (uniquep vars)
           (evaluation-eq-subset-p inits (corresponding-states inits vars)
                                   vars)))
)


(local
(defthm initial-states-are-evaluation-eq
  (implies (circuitp C)
           (evaluation-eq-subset-p 
            (initial-states (create-kripke C))
            (initial-states 
             (create-kripke 
              (cone-of-influence-reduction C vars)))
            (cone-variables vars C)))
  :hints (("Goal"
           :in-theory (disable subset-of-nil-is-nil 
                               subset-of-empty-is-empty))))
)

(local
(defthm corresponding-states-are-evaluation-eq-2
  (implies (uniquep vars)
           (evaluation-eq (corresponding-state init vars) init vars)))
)

(local
(defthm evaluation-eq-memberp-of-corresponding-states-2
  (implies (and (uniquep vars)
                (memberp init (corresponding-states inits vars)))
           (evaluation-eq-member-p  init inits
                                   vars)))
)

(local
(defthm evaluation-eq-subsets-reduction-2
  (implies (uniquep vars)
           (evaluation-eq-subset-p (corresponding-states inits vars) inits
                                   vars)))
)

(local
(defthm initial-states-are-evaluation-eq-2
  (implies (circuitp C)
           (evaluation-eq-subset-p
            (initial-states 
             (create-kripke 
              (cone-of-influence-reduction C vars)))
            (initial-states (create-kripke C))
            (cone-variables vars C))))
)

;; END of work on initial states.

;; OK, now let us work on showing that cone-of-influence-reduction produces a
;; circuit model. This will follow if the cone of influence reduction actually
;; produces a circuit. We prove that in the lemmas below.

;; We first prove that the initial states are only evaluations of the variables.

(local
(defthm initial-states-are-evaluations-p
  (implies (and (evaluation-p p variables)
                (subset vars variables)
                (uniquep variables))
           (evaluation-p (corresponding-state p vars) vars)))
)

(local
(defthm corresponding-states-only-evaluations-p
  (implies (and (only-evaluations-p init variables)
                (subset vars variables)
                (uniquep variables))
           (only-evaluations-p (corresponding-states init vars) vars)))
)

(local
(defthm initial-states-of-cone-of-influence-are-only-evaluations-p
  (implies (circuitp C)
           (only-evaluations-p 
            (initial-states
             (cone-of-influence-reduction C vars))
            (variables 
             (cone-of-influence-reduction C vars)))))
)

;; Next we work on strict-evaluation-list-p.

(local
(defthm not-memberp-to-corresponding-state
  (implies (not (memberp v vars))
           (not (<- (corresponding-state init vars) v))))
)

(local
(defthm corresponding-state-strict-evaluation-p
  (strict-evaluation-p (corresponding-state init vars) vars))
)

(local
(in-theory (disable strict-evaluation-p))
)

(local
(defthm initial-states-strict-evaluation-list-p
  (strict-evaluation-list-p vars (corresponding-states inits vars)))
)

(local
(defthm initial-cone-of-influence-states-are-strict-evaluation-list-p
  (strict-evaluation-list-p 
   (variables
    (cone-of-influence-reduction C vars))
   (initial-states 
    (cone-of-influence-reduction C vars)))
  :hints (("Goal"
           :in-theory (disable cone-variables))))
)

(local
(defthm variables-of-cone-are-unique-p
  (implies (circuitp C)
           (uniquep 
            (variables 
             (cone-of-influence-reduction C vars)))))
)


;; We come here to cons-list-p.


(local
(defun equation-equal-p (eqn-orig eqn-cone vars)
  (if (endp vars) T
    (and (equal (<- eqn-orig (first vars))
                (<- eqn-cone (first vars)))
         (equation-equal-p eqn-orig eqn-cone (rest vars)))))
)

(local
(defthm cons-list-p-equation-equal-reduction
  (implies (equation-equal-p eqn-orig eqn-cone vars)
           (equal (cons-list-p vars eqn-cone)
                  (cons-list-p vars eqn-orig))))
)

(local
(defthm find-equations-for-not-member-p
  (implies (not (memberp v vars))
           (equal (<- (find-all-equations vars equations eqn-rec) v)
                  (<- eqn-rec v))))
)

(local
(defthm cons-list-p-subset-reduction
  (implies (and (cons-list-p vars equations)
                (subset vars-prime vars))
           (cons-list-p vars-prime equations)))
)

(local
(defthm equations-of-cone-and-orig-are-equal
  (implies (uniquep vars)
           (equation-equal-p equations
                             (find-all-equations
                              vars equations eqn-rec)
                             vars))
  :hints (("Goal"
           :induct (find-all-equations vars equations eqn-rec)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm equations-of-cone-are-cons-list-p
  (implies (circuitp C)
           (cons-list-p (variables 
                         (cone-of-influence-reduction C vars))
                        (equations
                         (cone-of-influence-reduction C vars))))
  :hints (("Goal"
           :in-theory (disable find-all-equations find-all-variables
                               cons-list-p-equation-equal-reduction)
           :use ((:instance cons-list-p-equation-equal-reduction
                            (eqn-orig (equations C))
                            (eqn-cone 
                             (equations
                              (cone-of-influence-reduction C vars)))
                            (vars (variables 
                                   (cone-of-influence-reduction C vars))))))))
)

(local
(defthm find-variables-variables*-reduction
  (implies (memberp equation equations)
           (subset (find-variables equation)
                   (find-variables* equations))))
)

(local
(defthm find-variables-1-pass-reduction
  (implies (and (memberp v vars)
                (memberp equation (<- equations v)))
           (subset (find-variables equation)
                   (find-all-variables-1-pass vars equations)))
  :hints (("Subgoal *1/2"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :cases ((equal v (car vars))))
          ("Subgoal *1/2.1"
           :in-theory (disable find-variables-variables*-reduction)
           :use ((:instance find-variables-variables*-reduction
                            (equations (<- equations (first vars)))))))
  :rule-classes nil)
)

(local
(defthm find-all-variables-computes-closure
  (implies (and (memberp v (find-all-variables vars variables equations))
                (uniquep variables)
                (subset vars variables)
                (uniquep vars)
                (memberp equation (<- equations v)))
           (subset (find-variables equation)
                   (find-all-variables vars variables equations)))
  :hints (("Goal"
           :induct (find-all-variables vars variables equations)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)
          ("Subgoal *1/2" 
           :in-theory (enable set-equal)
           :use find-variables-1-pass-reduction)))
)

(local
(in-theory (disable find-all-variables))
)

(local
(defthm find-all-variables-is-equation-record-p
  (implies (and (subset vars variables)
                (uniquep vars)
                (uniquep variables))
           (consistent-equation-record-p
            (find-all-variables vars variables equations)
            equations))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable  find-all-variables-computes-closure)
           :use ((:instance (:definition consistent-equation-record-p)
                            (vars (find-all-variables vars variables
                                                      equations)))
                 (:instance find-all-variables-computes-closure
                            (v (mv-nth 0 
                                       (consistent-equation-record-p-witness
                                        (find-all-variables vars variables
                                                            equations)
                                        equations)))
                            (equation
                             (mv-nth 1 
                                     (consistent-equation-record-p-witness
                                      (find-all-variables vars variables
                                                          equations)
                                      equations))))))))
)

;; So we have proved that find-all-variables produces a consistent record for
;; the original equations. Now we have to prove that if two equations are
;; equation-equal-p, then they are consistent-equation-record-p at the same
;; time.

(local
(in-theory (disable consistent-equation-record-p))
)

(local
(defthm equation-equal-p-member-reduction
  (implies (and (equation-equal-p eqn-orig eqn-cone vars)
                (memberp v vars))
           (equal (<- eqn-cone v)
                  (<- eqn-orig v))))
)

(local
(defthm consistent-eqn-record-p-expanded
  (implies (and (consistent-equation-record-p vars eqn-orig)
                (uniquep vars)
                (memberp v vars)
                (memberp equation (<- eqn-orig v)))
           (subset (find-variables equation)
                   vars))
  :hints (("Goal"
           :use ((:instance consistent-equation-record-p-necc
                            (equations eqn-orig))))))
)

(local
(defthm equation-equal-p-to-consistent
  (implies (and (equation-equal-p eqn-orig eqn-cone vars)
                (uniquep vars)
                (consistent-equation-record-p vars eqn-orig))
           (consistent-equation-record-p vars eqn-cone))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable consistent-equation-record-p
                               consistent-equation-record-p-necc
                               mv-nth)
           :expand (consistent-equation-record-p vars eqn-cone)
           :use ((:instance  consistent-equation-record-p-necc
                             (equation eqn-orig))))))
)

(local
(in-theory (disable consistent-equation-record-p 
                    consistent-equation-record-p-necc))
)

(local
(defthm cone-of-influence-reduction-is-consistent
  (implies (circuitp C)
           (consistent-equation-record-p
            (variables (cone-of-influence-reduction C vars))
            (equations (cone-of-influence-reduction C vars))))
  :hints (("Goal"
           :use ((:instance equation-equal-p-to-consistent
                            (eqn-orig (equations C))
                            (eqn-cone 
                             (equations (cone-of-influence-reduction C vars)))
                            (vars (variables (cone-of-influence-reduction C vars))))))))
           
)

(local
(defthm cone-of-influence-reduction-is-circuit-p
  (implies (circuitp C)
           (circuitp (cone-of-influence-reduction C vars)))
  :hints (("Goal"
           :in-theory (disable circuitp cone-of-influence-reduction)
           :expand (circuitp (cone-of-influence-reduction C vars)))))
)

(local
(defthm cone-of-influence-reduction-produces-circuit-model
  (implies (circuitp C)
           (circuit-modelp (create-kripke (cone-of-influence-reduction C vars))))
  :hints (("Goal"
           :in-theory (disable circuitp circuit-modelp 
                               create-kripke
                               cone-of-influence-reduction))))
)

;; OK, so the last thing we need to prove is that the transitions of m and n
;; are well-formed-transition-p. That means that we have to prove that if two
;; states are evaluation-eq with respect to vars, then the next states are
;; evaluation-eq with respect to vars.

;; For simplifying the project let us first start with original circuit and get
;; to the cone of influence reduction.

;; OK, so what do we need? Let us first prove that if r is in next-states of p,
;; then there exists an equation consistent with equations that takes from p to
;; r.

;; We start with a couple of theorems about evaluation-eq

(local
(defthm evaluation-eq-is-reflexive
  (evaluation-eq x x vars))
)

(local
(defthm evaluation-eq-is-transitive
  (implies (and (evaluation-eq p q vars)
                (evaluation-eq q r vars))
           (evaluation-eq p r vars)))
)

;; Now to the argument. If r is in next states of p, then there is an equation
;; taking p to r.

;; We first prove that r is a valid next state of p.

(local
(defthm next-state-member-implies-consistent-equation
  (implies (memberp r (create-next-states-of-p p states vars equations))
           (next-state-is-ok p r vars equations)))
)

;; Now if next-state-is-ok, then we know that there is a consistent equation
;; that takes p to r.

(local
(defthm next-state-is-ok-to-consistent-p-equation
  (implies (next-state-is-ok p r vars equations)
           (consistent-p-equations 
            vars 
            (next-state-is-ok-witness p r vars equations)
            equations)))
)

(local
(defthm next-state-is-ok-p-to-actual
  (implies (next-state-is-ok p r vars equations)
           (evaluation-eq r (produce-next-state vars p 
                                                (next-state-is-ok-witness
                                                 p r vars equations))
                          vars)))
)

(local
(defthm thus-r-is-evaluation-eq-to-s
  (implies (and (next-state-is-ok p r vars-orig equations-orig)
                (evaluation-eq (produce-next-state vars-orig p
                                (next-state-is-ok-witness p r vars-orig
                                                          equations-orig))
                                s
                                vars-cone)
                (subset vars-cone vars-orig))
           (evaluation-eq r s vars-cone))
  :hints (("Goal"
           :in-theory (disable next-state-is-ok-p-to-actual
                               evaluation-eq-subset-reduction
                               next-state-is-ok)
           :do-not-induct t
           :use ((:instance next-state-is-ok-p-to-actual
                            (vars vars-orig)
                            (equations equations-orig))
                 (:instance evaluation-eq-subset-reduction
                            (p r)
                            (q  (PRODUCE-NEXT-STATE
                                 VARS-ORIG P
                                 (NEXT-STATE-IS-OK-WITNESS P R VARS-ORIG
                                                           EQUATIONS-ORIG)))
                            (vars vars-orig)
                            (vars-prime vars-cone))))))
)

;; Thus r is evaluation-eq with respect to s if we can show that
;; produce-next-state produces something evaluation-eq to s. Now to show that
;; this implies r is evaluation-eq-member-p of transition of q, we need to show
;; that s is a member of states-cone and that there is a consistent equation
;; with respect to cone that takes q to s. Let us see that this analysis is
;; accurate.


(local
(defthm next-state-is-ok-from-consistent-eqn
  (implies (and (consistent-p-equations vars eqn equations)
                (evaluation-eq q (produce-next-state vars p eqn) vars))
           (next-state-is-ok p q vars equations)))
)

(local
(in-theory (disable next-state-is-ok))
)

(local
(defthm memberp-of-next-state-from-consistent-equation
  (implies (and (memberp s states-cone)
                (next-state-is-ok q s vars-cone equations-cone))
           (memberp s (create-next-states-of-p q states-cone vars-cone
                                               equations-cone))))
)

(local
(defthm memberp-not-using-next-states
  (implies (and (memberp s states-cone)
                (consistent-p-equations vars-cone eqn equations-cone)
                (evaluation-eq s (produce-next-state vars-cone q eqn) vars-cone))
           (memberp s (create-next-states-of-p q states-cone vars-cone equations-cone))))
)

;; OK, so now, how do we show that s is a member of states? This is because
;; states are all-evaluations-p, and s is an evaluation-p as we will see.


(local
(defthm member-of-next-states-from-all-evaluations-p
  (implies (and (all-evaluations-p states-cone vars-cone)
                (evaluation-p s vars-cone)
                (consistent-p-equations vars-cone eqn equations-cone)
                (evaluation-eq s (produce-next-state vars-cone q eqn) vars-cone))
           (memberp
            (evaluation-eq-member s states-cone vars-cone)
            (create-next-states-of-p q states-cone vars-cone equations-cone)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable memberp-not-using-next-states)
           :use ((:instance memberp-not-using-next-states
                            (s (evaluation-eq-member s states-cone vars-cone)))
                 (:instance evaluation-eq-is-symmetric
                            (p s)
                            (q (evaluation-eq-member s states-cone vars-cone))
                            (vars vars-cone))))))
)

(local
(defthm evaluation-eq-and-memberp-to-evaluation-eq-memberp
  (implies (and (memberp q states)
                (evaluation-eq p q vars))
           (evaluation-eq-member-p p states vars)))
)

(defthm evaluation-eq-memberp-from-all-evaluations-p
  (implies (and (all-evaluations-p states-cone vars-cone)
                (evaluation-p s vars-cone)
                (consistent-p-equations vars-cone eqn equations-cone)
                (evaluation-eq s (produce-next-state vars-cone q eqn)
                               vars-cone))
           (evaluation-eq-member-p 
            s (create-next-states-of-p q states-cone vars-cone equations-cone)
            vars-cone))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable
                       evaluation-eq-and-memberp-to-evaluation-eq-memberp)
           :use ((:instance evaluation-eq-and-memberp-to-evaluation-eq-memberp
                            (q (evaluation-eq-member s states-cone vars-cone))
                            (p s)
                            (vars vars-cone)
                            (states (create-next-states-of-p 
                                     q states-cone vars-cone
                                     equations-cone)))))))

(local
(defthm evaluation-eq-and-memberp-to-memberp
  (implies (and (evaluation-eq p q vars)
                (evaluation-eq-member-p q states vars))
           (evaluation-eq-member-p p states vars)))
)

(local
(defthm next-state-of-orig-to-evaluation-eq-member-p
  (implies (and (memberp r (create-next-states-of-p p states-orig vars-orig
                                                    equations-orig))
               (evaluation-eq (produce-next-state vars-orig p
                                (next-state-is-ok-witness p r vars-orig
                                                          equations-orig))
                              s
                              vars-cone)
                (subset vars-cone vars-orig)
                (all-evaluations-p states-cone vars-cone)
                (evaluation-p s vars-cone)
                (consistent-p-equations vars-cone eqn equations-cone)
                (evaluation-eq s (produce-next-state vars-cone q eqn)
                               vars-cone))
           (evaluation-eq-member-p 
            r (create-next-states-of-p q states-cone vars-cone equations-cone)
            vars-cone))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable thus-r-is-evaluation-eq-to-s)
           :use thus-r-is-evaluation-eq-to-s)))
)

;; The theorem above guarantees that if we can get an s and an eqn with the
;; properties mentioned then we will be done. Our choice of s is
;; (produce-next-state vars-cone q eqn). Hence the only thing to prove is that
;; we can get a corresponding equation for s.

(local
(defun create-corresponding-equation (vars equation-record vars-prime eqn eq-rec)
  (if (endp vars) eq-rec
    (-> (create-corresponding-equation (rest vars) equation-record vars-prime
                                       eqn eq-rec)
        (first vars)
        (if (memberp (first vars) vars-prime) 
            (<- eqn (first vars))
          (first (<- equation-record (first vars)))))))
)

;; OK, so why is this equation consistent with the cone? The argument is that
;; the cone of influence is well-formed-equation-record-p, and equation-equal-p
;; with respect to the variables of the cone.

(local
(defthm equation-equal-to-set-reduction
  (implies (not (memberp v vars))
           (equal (equation-equal-p eqn-orig (-> eqn-cone v a) vars)
                  (equation-equal-p eqn-orig eqn-cone vars))))
)

(local
(defthm create-corresponding-equation-is-equation-equal
  (implies (and (subset vars-cone vars-orig)
                (uniquep vars-cone))
           (equation-equal-p eqn-orig (create-corresponding-equation 
                                       vars-cone eqn-cone
                                       vars-orig eqn-orig eq-rec)
                             
                             vars-cone)))
)

(local
(defthm cons-consistent-eqn
  (implies (and (consistent-p-equations vars eqn equation-record)
                (memberp equation (<- equation-record v)))
           (consistent-p-equations (cons v vars) (-> eqn v equation)
                                   equation-record))
  :hints (("Subgoal *1/4"
           :cases ((equal v (car vars))))))
)

(local
(defthm consistent-p-equation-memberp-reduction
  (implies (and (consistent-p-equations vars eqn equations)
                (memberp v vars))
           (memberp (<- eqn v) (<- equations v))))
)

(local
(defthm consistent-set-not-member
  (implies (not (memberp v vars))
           (equal (consistent-p-equations vars (-> eqn v a) equations)
                  (consistent-p-equations vars eqn equations))))
)

(local
(defthm equation-equal-p-to-consistent-equation
  (implies (and (equation-equal-p eqn-orig eqn-cone vars)
                (consistent-p-equations vars eqn eqn-orig))
           (consistent-p-equations vars eqn eqn-cone)))
)

(local
(defthm consistent-p-equations-to-consistent-p-equations
  (implies (and (consistent-p-equations vars-orig eqn eqn-orig)
                (cons-list-p vars-cone eqn-cone)
                (equation-equal-p eqn-orig eqn-cone vars-cone)
                (uniquep vars-orig)
                (uniquep vars-cone))
           (consistent-p-equations 
            vars-cone
            (create-corresponding-equation vars-cone eqn-cone vars-orig eqn
                                           eq-rec)
            eqn-cone))
  :otf-flg t
  :hints (("Goal"
           :induct (create-corresponding-equation vars-cone eqn-cone
                                                  vars-orig eqn eq-rec)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

;; OK so now we have created an equation eqn that is consistent with respect to
;; the cone. So the final proof requirement is that s is evaluation-eq to the
;; application of this equation.

(local
(defun closed-eqn-record-p (eqn vars vars-prime)
  (if (endp vars) T
    (and (subset (find-variables (<- eqn (first vars))) vars-prime)
         (closed-eqn-record-p eqn (rest vars) vars-prime))))
)

;; This predicate ensures that the variables of eqn are subsets of
;; vars-prime. Now let us show that this notion follows from equation-record-p.

(local
(defthm closed-eqn-record-p-from-consistent-equation-record-p
  (implies (and (consistent-equation-record-p vars-prime equations)
                (uniquep vars-prime)
                (subset vars vars-prime)
                (consistent-p-equations vars eqn equations))
           (closed-eqn-record-p eqn vars vars-prime))
  :hints (("Subgoal *1/5"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

;; And thus, by concretizing it, we have the following theorem:

(local
(defthm closed-eqn-record-p-true-concretized
  (implies (and (consistent-equation-record-p vars equations)
                (uniquep vars)
                (consistent-p-equations vars eqn equations))
           (closed-eqn-record-p eqn vars vars)))
)

(local
(defthm apply-equation-produces-equal
  (implies (and (evaluation-p p vars)
                (evaluation-p q vars)
                (subset (find-variables equation) vars)
                (evaluation-eq p q vars))
           (equal (apply-equation equation p)
                  (apply-equation equation q)))
  :hints (("Goal"
           :induct (apply-equation equation p))))
)

(local
(defthm produce-next-state-not-memberp-vars-reduction
  (implies (not (memberp v vars))
           (equal (<- (produce-next-state vars p equations) v)
                  (<- p v))))
)

(local
(defthm produce-next-state-vars-reduction
  (implies (and (memberp v vars)
                (uniquep vars))
           (equal (<- (produce-next-state vars p equations) v)
                  (apply-equation (<- equations v) p))))
)

(local
(defthm evaluation-eq-set-reduction
  (implies (and (evaluation-eq p q vars)
                (not (memberp v vars)))
           (evaluation-eq (-> p v a) (-> q v b) vars)))
)

(local
(defthm produce-next-state-is-evaluation-eq
  (implies (and (evaluation-p p vars-prime)
                (uniquep vars-prime)
                (evaluation-p q vars-prime)
                (uniquep vars-prime)
                (uniquep vars)
                (subset vars vars-prime)
                (evaluation-eq p q vars-prime)
                (closed-eqn-record-p eqn-cone vars vars-prime)
                (equation-equal-p eqn-orig eqn-cone vars))
           (evaluation-eq 
            (produce-next-state vars p eqn-orig)
            (produce-next-state vars q eqn-cone)
            vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable apply-equation-produces-equal))
          ("Subgoal *1/6"
           :use ((:instance apply-equation-produces-equal
                            (vars vars-prime)
                            (equation (<- eqn-cone (first vars))))))))
)

(local
(defthm produce-next-state-is-evaluation-eq-concretized
  (implies (and (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (uniquep vars-cone)
                (consistent-equation-record-p vars-cone equations-cone)
                (consistent-p-equations vars-cone eqn-cone equations-cone)
                (equation-equal-p eqn-orig eqn-cone vars-cone))
           (evaluation-eq 
            (produce-next-state vars-cone p eqn-orig)
            (produce-next-state vars-cone q eqn-cone)
            vars-cone)))
)

(local
(defthm produce-next-state-evaluation-eq-reduction
  (implies (and (uniquep vars-orig)
                (uniquep vars-cone)
                (subset vars-cone vars-orig))
           (evaluation-eq (produce-next-state vars-orig p eqn-orig)
                          (produce-next-state vars-cone p eqn-orig)
                          vars-cone)))
)

(local
(defthm produce-next-state-fully-concretized
  (implies (and (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (subset vars-cone vars-orig)
                (consistent-equation-record-p vars-cone equations-cone)
                (consistent-p-equations vars-cone eqn-cone equations-cone)
                (equation-equal-p eqn-orig eqn-cone vars-cone))
           (evaluation-eq (produce-next-state vars-orig p eqn-orig)
                          (produce-next-state vars-cone q eqn-cone)
                          vars-cone))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable evaluation-eq-is-transitive
                               produce-next-state-is-evaluation-eq-concretized)
           :use ((:instance produce-next-state-is-evaluation-eq-concretized)
                 (:instance evaluation-eq-is-transitive
                            (p (produce-next-state vars-orig p eqn-orig))
                            (q (produce-next-state vars-cone p eqn-orig))
                            (r (produce-next-state vars-cone q eqn-cone))
                            (vars vars-cone))))))
)

(local
(defthm produce-next-state-for-equation-of-choice
  (implies (and (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (cons-list-p vars-cone equations-cone)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-p-equations vars-orig eqn-orig equations-orig)
                (consistent-equation-record-p vars-cone equations-cone)
                (subset vars-cone vars-orig))
           (evaluation-eq
            (produce-next-state vars-orig p eqn-orig)
            (produce-next-state 
             vars-cone q
             (create-corresponding-equation
              vars-cone equations-cone vars-orig eqn-orig eq-rec))
            vars-cone)))
)

(local
(in-theory (disable apply-equation-produces-equal))
)
 
(local                              
(defthm boolean-p-apply-equation
  (implies (and (evaluation-p p vars)
                (subset (find-variables equation) vars))
           (booleanp (apply-equation equation p)))
  :hints (("Goal"
           :induct (apply-equation equation p))))
)

(local
(defthm evaluation-p-set-reduction
  (implies (and (booleanp a)
                (evaluation-p p vars))
           (evaluation-p (-> p v a) vars))
  :hints (("Subgoal *1/4"
           :cases ((equal v (car vars))))))
)

(local
(defthm produce-next-state-is-evaluation-p
  (implies (and (evaluation-p p vars-prime)
                (subset vars vars-prime)
                (uniquep vars)
                (uniquep vars-prime)
                (closed-eqn-record-p eqn vars vars-prime))
           (evaluation-p (produce-next-state vars p eqn) vars-prime)))
)

(local
(defthm next-state-is-evaluation-p-concretized
  (implies (and (evaluation-p p vars)
                (uniquep vars)
                (consistent-equation-record-p vars equations)
                (consistent-p-equations vars eqn equations))
           (evaluation-p (produce-next-state vars p eqn) vars)))
)

(local
(defthm r-is-evaluation-eq-member-p-with-respect-to-states
  (implies (and (memberp r (create-next-states-of-p p states-orig vars-orig
                                                    equations-orig))
                (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (subset vars-cone vars-orig)
                (evaluation-p p vars-orig)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (cons-list-p vars-cone equations-cone)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-equation-record-p vars-cone equations-cone)
                (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-member-p 
             r (create-next-states-of-p q states-cone vars-cone equations-cone)
             vars-cone))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable next-state-of-orig-to-evaluation-eq-member-p)
           :use ((:instance next-state-of-orig-to-evaluation-eq-member-p
                            (s (produce-next-state vars-orig p
                                (next-state-is-ok-witness p r vars-orig
                                                          equations-orig)))
                            (eqn (create-corresponding-equation
                                  vars-cone equations-cone vars-orig 
                                  (next-state-is-ok-witness p r vars-orig
                                                          equations-orig)
                                  eq-rec)))))
          ("Subgoal 2"
           :in-theory (disable evaluationp-for-subset
                               next-state-is-evaluation-p-concretized)
           :use ((:instance next-state-is-evaluation-p-concretized
                            (eqn (next-state-is-ok-witness 
                                  p r vars-orig equations-orig))
                            (equations equations-orig)
                            (vars vars-orig))
                 (:instance evaluationp-for-subset
                            (st  (PRODUCE-NEXT-STATE
                                  VARS-ORIG P
                                  (NEXT-STATE-IS-OK-WITNESS P R VARS-ORIG
                                                            EQUATIONS-ORIG)))
                            (variables vars-orig)
                            (vars vars-cone))))
          ("Subgoal 1"
           :in-theory (disable
                       consistent-p-equations-to-consistent-p-equations)
           :use ((:instance consistent-p-equations-to-consistent-p-equations
                            (eqn-orig equations-orig)
                            (eqn-cone equations-cone)
                            (eqn (next-state-is-ok-witness p r vars-orig
                                                           equations-orig)))))))

)

(local
(defthm evaluation-eq-subset-p-orig->cone
  (implies (and (subset l (create-next-states-of-p p states-orig vars-orig
                                                    equations-orig))
                (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (subset vars-cone vars-orig)
                (evaluation-p p vars-orig)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (cons-list-p vars-cone equations-cone)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-equation-record-p vars-cone equations-cone)
                (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-subset-p 
             l (create-next-states-of-p q states-cone vars-cone equations-cone)
             vars-cone)))
)

(local
(defthm evaluation-eq-subset-orig->cone-concretized
  (implies (and (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (subset vars-cone vars-orig)
                (only-evaluations-p states-orig vars-orig)
                (memberp p states-orig)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (cons-list-p vars-cone equations-cone)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-equation-record-p vars-cone equations-cone)
                (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-subset-p 
             (create-next-states-of-p p states-orig vars-orig
                                      equations-orig)
             (create-next-states-of-p q states-cone vars-cone equations-cone)
             vars-cone))
  :hints (("Goal"
           :in-theory (disable evaluation-eq-subset-p-orig->cone)
           :use ((:instance evaluation-eq-subset-p-orig->cone
                            (l  (create-next-states-of-p p states-orig vars-orig
                                      equations-orig)))))))
)

(local
(defthm equation-equal-is-symmetric
  (equal (equation-equal-p eqn-orig eqn-cone vars)
         (equation-equal-p eqn-cone eqn-orig vars))
  :rule-classes nil)
)

(local
(defthm equation-equal-to-set-reduction-2
  (implies (not (memberp v vars))
           (equal (equation-equal-p (-> eqn-orig v a) eqn-cone vars)
                  (equation-equal-p eqn-orig eqn-cone vars))))
)

(local
(defthm memberp-to-create-equation-reduction
  (implies (and (memberp v vars-cone)
                (memberp v vars-orig))
           (equal (<- (create-corresponding-equation vars-orig eqn-orig
                                                     vars-cone eqn-cone 
                                                     eq-rec)
                      v)
                  (<- eqn-cone v)))
  :hints (("Subgoal *1/3.2"
           :cases ((equal v (car vars-orig))))))
)

(local
(defthm not-memberp-to-create-equation
  (implies (not (memberp v vars-orig))
           (equal (<- (create-corresponding-equation vars-orig eqn-orig
                                                     vars-cone eqn-cone eq-rec)
                      v)
                  (<- eq-rec v))))
)

(local
(defthm memberp-equation-reduction-2
  (implies (and (not (memberp v vars-cone))
                (memberp v vars-orig))
           (equal (<- (create-corresponding-equation vars-orig eqn-orig
                                                     vars-cone eqn-cone eq-rec)
                      v)
                  (first (<- eqn-orig v))))
  :hints (("Subgoal *1/3"
           :cases ((equal v (car vars-orig))))))
)
 
(local                 
(defthm create-corresponding-equation-is-equation-equal-2
  (implies (and (subset vars-cone vars-orig)
                (subset vars vars-cone)
                (uniquep vars-orig)
                (uniquep vars-cone))
           (equation-equal-p (create-corresponding-equation 
                              vars-orig eqn-orig
                              vars-cone eqn-cone eq-rec)
                            eqn-cone vars))
  :otf-flg t
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize))))
)

(local
(defthm produce-next-state-for-equation-of-choice-2
  (implies (and (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (cons-list-p vars-orig equations-orig)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-p-equations vars-cone eqn-cone equations-cone)
                (consistent-equation-record-p vars-cone equations-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (subset vars-cone vars-orig))
           (evaluation-eq
            (produce-next-state 
             vars-orig p
             (create-corresponding-equation
              vars-orig equations-orig vars-cone eqn-cone eq-rec))
            (produce-next-state vars-cone q eqn-cone)
            vars-cone)))
)

(local
(defthm and-thus-for-vars-cone
   (implies (and (all-evaluations-p states-orig vars-orig)
                 (evaluation-p r vars-orig)
                 (subset vars-cone vars-orig)
                 (consistent-p-equations vars-orig eqn equations-orig)
                 (evaluation-eq r (produce-next-state vars-orig p eqn)
                                vars-orig))
            (evaluation-eq-member-p 
             r (create-next-states-of-p p states-orig vars-orig equations-orig)
             vars-cone))
   :hints (("Goal"
            :in-theory (disable evaluation-eq-member-subset-reduction)
            :use ((:instance evaluation-eq-member-subset-reduction
                             (init r)
                             (vars vars-orig)
                             (vars-prime vars-cone)
                             (inits (create-next-states-of-p 
                                     p states-orig vars-orig
                                     equations-orig)))))))
)

(local
(defthm thus-r-is-evaluation-eq-to-s-2
  (implies (and (next-state-is-ok q s vars-cone equations-cone)
                (evaluation-eq  (produce-next-state 
                                  vars-cone q
                                  (next-state-is-ok-witness q s vars-cone 
                                                            equations-cone))
                                r
                               
                               vars-cone))
           (evaluation-eq s r vars-cone))
  :rule-classes nil)
)

;; and then suitably polish it


(local
(defthm thus-polished-r-is-evaluation-eq-to-s-2
  (implies (and (memberp s (create-next-states-of-p q states-cone vars-cone
                                                    equations-cone))
                (evaluation-eq r (produce-next-state
                                  vars-cone q
                                  (next-state-is-ok-witness
                                   q s vars-cone equations-cone))
                               vars-cone))
           (evaluation-eq r s vars-cone))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable next-state-is-ok 
                               next-state-member-implies-consistent-equation)
           :use ((:instance next-state-member-implies-consistent-equation
                            (p q)
                            (r s)
                            (vars vars-cone)
                            (states states-cone)
                            (equations equations-cone))
                 (:instance thus-r-is-evaluation-eq-to-s-2)
                 (:instance evaluation-eq-is-symmetric
                            (p r)
                            (q s)
                            (vars vars-cone))
                 (:instance evaluation-eq-is-symmetric
                            (p r)
                            (vars vars-cone)
                            (q (produce-next-state
                                  vars-cone q
                                  (next-state-is-ok-witness
                                   q s vars-cone equations-cone))))))))
)

(local
(defthm evaluation-eq-member-p-from-memberp
  (implies (and (evaluation-eq s r vars)
                (evaluation-eq-member-p r states vars))
           (evaluation-eq-member-p s states vars)))
)

(local
(defthm next-state-of-orig-to-evaluation-eq-member-p-2
  (implies (and (memberp s (create-next-states-of-p q states-cone vars-cone
                                                    equations-cone))
               (evaluation-eq r (produce-next-state 
                                 vars-cone q
                                 (next-state-is-ok-witness q s vars-cone
                                                           equations-cone))
                              vars-cone)
               (uniquep vars-orig)
               (uniquep vars-cone)
               (subset vars-cone vars-orig)
               (all-evaluations-p states-orig vars-orig)
               (evaluation-p r vars-orig)
               (consistent-p-equations vars-orig eqn equations-orig)
               (evaluation-eq r (produce-next-state vars-orig p eqn)
                              vars-orig))
           (evaluation-eq-member-p 
            s (create-next-states-of-p p states-orig vars-orig equations-orig)
            vars-cone))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable ;; produce-next-state-evaluation-eq-reduction
                       and-thus-for-vars-cone
                       thus-polished-r-is-evaluation-eq-to-s-2)
           :use ((:instance thus-polished-r-is-evaluation-eq-to-s-2)
                 (:instance and-thus-for-vars-cone)
                 (:instance evaluation-eq-is-symmetric
                            (p r)
                            (q s)
                            (vars vars-cone))))))
)

(local
(defthm consistent-p-equations-to-consistent-p-equations-2
  (implies (and (consistent-p-equations vars-cone eqn equations-cone)
                (cons-list-p vars-orig equations-orig)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (uniquep vars-orig)
                (uniquep vars-cone))
           (consistent-p-equations 
            vars-orig
            (create-corresponding-equation
             vars-orig equations-orig vars-cone eqn eqn-rec)
            equations-orig))
  :hints (("Goal"
           :induct (create-corresponding-equation
                    vars-orig equations-orig vars-cone eqn eqn-rec)
          :do-not-induct t)
          ("Subgoal *1/2"
           :use ((:instance consistent-p-equation-memberp-reduction
                            (vars vars-cone)
                            (v (car vars-orig))
                            (equations equations-cone))))))
)

(local            
(defthm next-state-cone->orig-thus-settled
   (implies (and (memberp s (create-next-states-of-p q states-cone vars-cone
                                                    equations-cone))
                (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (subset vars-cone vars-orig)
                (evaluation-p p vars-orig)
                (evaluation-p q vars-cone)
                (all-evaluations-p states-orig vars-orig)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (cons-list-p vars-orig equations-orig)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (consistent-equation-record-p vars-cone equations-cone)
                (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-member-p 
             s (create-next-states-of-p p states-orig vars-orig equations-orig)
             vars-cone))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable
                        consistent-p-equations-to-consistent-p-equations-2
                        next-state-of-orig-to-evaluation-eq-member-p-2)
            :use ((:instance next-state-of-orig-to-evaluation-eq-member-p-2
                              (r (produce-next-state 
                                  vars-orig p
                                  (create-corresponding-equation
                                   vars-orig equations-orig vars-cone
                                   (next-state-is-ok-witness q s vars-cone
                                                             equations-cone)
                                   eq-rec)))
                            (eqn (create-corresponding-equation
                                  vars-orig equations-orig vars-cone 
                                  (next-state-is-ok-witness q s vars-cone
                                                          equations-cone)
                                  eq-rec)))
                  (:instance next-state-is-evaluation-p-concretized
                             (vars vars-orig)
                             (equations equations-orig)
                             (eqn (create-corresponding-equation
                                  vars-orig equations-orig vars-cone 
                                  (next-state-is-ok-witness q s vars-cone
                                                          equations-cone)
                                  eq-rec)))
                  (:instance consistent-p-equations-to-consistent-p-equations-2
                              (eqn-rec eq-rec)
                              (eqn (next-state-is-ok-witness q s vars-cone
                                                             equations-cone)))))))

)

(local
(defthm next-state-cone->orig-concretized
   (implies (and (subset l (create-next-states-of-p q states-cone vars-cone
                                                    equations-cone))
                (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (subset vars-cone vars-orig)
                (evaluation-p p vars-orig)
                (evaluation-p q vars-cone)
                (all-evaluations-p states-orig vars-orig)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (cons-list-p vars-orig equations-orig)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (consistent-equation-record-p vars-cone equations-cone)
                (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-subset-p 
             l (create-next-states-of-p p states-orig vars-orig equations-orig)
             vars-cone)))
)

(local
(defthm and-fully-concretized-cone->orig
   (implies (and (evaluation-p p vars-cone)
                 (evaluation-p q vars-cone)
                 (evaluation-eq p q vars-cone)
                 (consistent-equation-record-p vars-orig equations-orig)
                 (subset vars-cone vars-orig)
                 (only-evaluations-p states-orig vars-orig)
                 (only-evaluations-p states-cone vars-cone)
                 (memberp p states-orig)
                 (memberp q states-cone)
                 (evaluation-p q vars-cone)
                 (all-evaluations-p states-orig vars-orig)
                 (uniquep vars-orig)
                 (uniquep vars-cone)
                 (cons-list-p vars-orig equations-orig)
                 (equation-equal-p equations-orig equations-cone vars-cone)
                 (consistent-equation-record-p vars-orig equations-orig)
                 (consistent-equation-record-p vars-cone equations-cone)
                 (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-subset-p 
             (create-next-states-of-p q states-cone vars-cone
                                      equations-cone)
            (create-next-states-of-p p states-orig vars-orig equations-orig)
             vars-cone))
   :hints (("Goal"
            :in-theory (disable next-state-cone->orig-concretized)
            :use ((:instance  next-state-cone->orig-concretized
                              (l (create-next-states-of-p q states-cone vars-cone
                                                          equations-cone)))))))
)

(local
(in-theory (disable create-next-states-of-p))
)

(local
(defthm not-member-p-to-next-states
  (implies (not (memberp p states))
           (equal (<- (create-next-states states states-prime vars equations)
                      p)
                  nil)))
)

(local
(defthm create-next-states-to-next-state-of-p
  (implies (memberp p states)
           (equal (<- (create-next-states states states-prime vars equations) 
                      p)
                  (create-next-states-of-p p states-prime vars equations)))
  :hints (("Subgoal *1/3"
           :cases ((equal p (car states))))))
)

(local
(defthm well-formed-transition-p-aux-orig->cone
   (implies (and (evaluation-p p vars-cone)
                (evaluation-p q vars-cone)
                (evaluation-eq p q vars-cone)
                (consistent-equation-record-p vars-orig equations-orig)
                (subset vars-cone vars-orig)
                (only-evaluations-p states-orig vars-orig)
                (memberp p states-orig)
                (uniquep vars-orig)
                (uniquep vars-cone)
                (cons-list-p vars-cone equations-cone)
                (memberp q states-cone)
                (only-evaluations-p states-cone vars-cone)
                (equation-equal-p equations-orig equations-cone vars-cone)
                (consistent-equation-record-p vars-cone equations-cone)
                (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-subset-p 
             (<- (create-next-states states-orig states-orig vars-orig
                                     equations-orig)
                 P)
             (<- (create-next-states states-cone states-cone vars-cone
                                     equations-cone)
                 Q)
             vars-cone)))
)

(local
(defthm well-formed-transition-p-aux-cone->orig
   (implies (and (evaluation-p p vars-cone)
                 (evaluation-p q vars-cone)
                 (evaluation-eq p q vars-cone)
                 (consistent-equation-record-p vars-orig equations-orig)
                 (subset vars-cone vars-orig)
                 (only-evaluations-p states-orig vars-orig)
                 (only-evaluations-p states-cone vars-cone)
                 (memberp p states-orig)
                 (memberp q states-cone)
                 (evaluation-p q vars-cone)
                 (all-evaluations-p states-orig vars-orig)
                 (uniquep vars-orig)
                 (uniquep vars-cone)
                 (cons-list-p vars-orig equations-orig)
                 (equation-equal-p equations-orig equations-cone vars-cone)
                 (consistent-equation-record-p vars-orig equations-orig)
                 (consistent-equation-record-p vars-cone equations-cone)
                 (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-subset-p 
             (<- (create-next-states states-cone states-cone vars-cone
                                     equations-cone)
                 q)
             (<- (create-next-states states-orig states-orig vars-orig
                                     equations-orig)
                 p)
             vars-cone)))
)

(local
(defthm well-formed-transition-p-aux-cone->orig-concretized
   (implies (and (evaluation-p p vars-cone)
                 (evaluation-p q vars-cone)
                 (evaluation-eq q p vars-cone)
                 (consistent-equation-record-p vars-orig equations-orig)
                 (subset vars-cone vars-orig)
                 (only-evaluations-p states-orig vars-orig)
                 (only-evaluations-p states-cone vars-cone)
                 (memberp p states-orig)
                 (memberp q states-cone)
                 (evaluation-p q vars-cone)
                 (all-evaluations-p states-orig vars-orig)
                 (uniquep vars-orig)
                 (uniquep vars-cone)
                 (cons-list-p vars-orig equations-orig)
                 (equation-equal-p equations-orig equations-cone vars-cone)
                 (consistent-equation-record-p vars-orig equations-orig)
                 (consistent-equation-record-p vars-cone equations-cone)
                 (all-evaluations-p states-cone vars-cone))
            (evaluation-eq-subset-p 
             (<- (create-next-states states-cone states-cone vars-cone
                                     equations-cone)
                 q)
             (<- (create-next-states states-orig states-orig vars-orig
                                     equations-orig)
                 p)
             vars-cone))
   :hints (("Goal"
            :in-theory (disable and-fully-concretized-cone->orig
                                evaluation-eq-subset-p
                                evaluation-eq-member-p
                                 next-state-cone->orig-concretized
                                well-formed-transition-p-aux-cone->orig)
            :use ((:instance well-formed-transition-p-aux-cone->orig)
                  (:instance evaluation-eq-is-symmetric
                             (vars vars-cone))))))
)

(local
(in-theory (disable create-all-evaluations find-all-variables
                    only-evaluations-p
                    all-evaluations-p
                    strict-evaluation-p
                    only-all-truths-p
                    label-subset-vars
                    transition-subset-p
                    next-states-in-states
                    cons-list-p
                    consistent-equation-record-p
                    uniquep
                    subset
                    find-all-equations create-label-fn))
)

(local
(in-theory (enable well-formed-transition-p))
)

(local
(defthm orig-cone-cone-is-well-formed-transition-p
  (implies (circuitp C)
           (well-formed-transition-p
            (states (create-kripke C))
            (transition (create-kripke C))
            (states 
             (create-kripke
              (cone-of-influence-reduction C vars)))
            (transition 
             (create-kripke 
              (cone-of-influence-reduction C vars)))
            (cone-variables vars C)))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize fertilize)
           :do-not-induct t
           :in-theory (disable well-formed-transition-p-aux-orig->cone 
                               create-kripke-produces-circuit-model)
           :use ((:instance well-formed-transition-p-aux-orig->cone
                            (states-orig (states (create-kripke C)))
                            (states-cone (states
                                          (create-kripke 
                                           (cone-of-influence-reduction 
                                            C vars))))
                            (vars-orig (variables C))
                            (vars-cone (variables 
                                        (cone-of-influence-reduction C vars)))
                            (equations-orig (equations C))
                            (equations-cone (equations 
                                             (cone-of-influence-reduction C
                                                                          vars)))
                            (p (car (well-formed-transition-p-witness
                                     (states (create-kripke C))
                                     (transition (create-kripke C))
                                     (states (create-kripke 
                                              (cone-of-influence-reduction C
                                                                           vars)))
                                     (transition
                                      (create-kripke 
                                       (cone-of-influence-reduction C vars)))
                                     (variables (cone-of-influence-reduction C
                                                                             vars)))))
                            (q (mv-nth 1 
                                       (well-formed-transition-p-witness
                                     (states (create-kripke C))
                                     (transition (create-kripke C))
                                     (states (create-kripke 
                                              (cone-of-influence-reduction C
                                                                           vars)))
                                     (transition
                                      (create-kripke 
                                       (cone-of-influence-reduction C vars)))
                                     (variables (cone-of-influence-reduction C
                                                                             vars))))))
                 (:instance create-kripke-produces-circuit-model)
                 (:instance create-kripke-produces-circuit-model
                            (C (cone-of-influence-reduction C vars)))
                 (:instance cone-of-influence-reduction-is-circuit-p)))))
)

(local
(defthm cone-orig-is-well-formed-transition-p
  (implies (circuitp C)
           (well-formed-transition-p
            (states 
             (create-kripke
              (cone-of-influence-reduction C vars)))
            (transition 
             (create-kripke 
              (cone-of-influence-reduction C vars)))
            (states (create-kripke C))
            (transition (create-kripke C))
            (cone-variables vars C)))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize fertilize)
           :do-not-induct t
           :in-theory (disable well-formed-transition-p-aux-orig->cone 
                               create-kripke-produces-circuit-model)
           :use ((:instance well-formed-transition-p-aux-cone->orig-concretized
                            (states-orig (states (create-kripke C)))
                            (states-cone (states
                                          (create-kripke 
                                           (cone-of-influence-reduction 
                                            C vars))))
                            (vars-orig (variables C))
                            (vars-cone (variables 
                                        (cone-of-influence-reduction C vars)))
                            (equations-orig (equations C))
                            (equations-cone (equations 
                                             (cone-of-influence-reduction C
                                                                          vars)))
                            (q (car (well-formed-transition-p-witness
                                     (states (create-kripke 
                                              (cone-of-influence-reduction C vars)))
                                     (transition (create-kripke 
                                                  (cone-of-influence-reduction
                                                   C vars)))
                                     (states (create-kripke C))
                                     (transition (create-kripke C))

                                     (variables (cone-of-influence-reduction C
                                                                             vars)))))
                             (p (mv-nth 1 
                                        (well-formed-transition-p-witness
                                         (states (create-kripke 
                                                  (cone-of-influence-reduction C vars)))
                                         (transition (create-kripke 
                                                      (cone-of-influence-reduction
                                                       C vars)))
                                         (states (create-kripke C))
                                         (transition (create-kripke C))
                                         (variables (cone-of-influence-reduction C
                                                                             vars))))))
                              
                 (:instance create-kripke-produces-circuit-model)
                 (:instance create-kripke-produces-circuit-model
                            (C (cone-of-influence-reduction C vars)))
                 (:instance cone-of-influence-reduction-is-circuit-p)))))
)

(local
(in-theory (disable well-formed-transition-p create-kripke
                    cone-of-influence-reduction
                    cone-variables 
                    circuit-modelp circuitp))
)

(local
(defthm cone-of-influence-is-c-bisimi-equiv
  (implies (circuitp C)
           (c-bisim-equiv (create-kripke C)
                           (create-kripke (cone-of-influence-reduction C vars))
                           (cone-variables vars C))))
)

(local
(in-theory (disable c-bisim-equiv))
)

(local
(defthm restricted-formula-of-vars-is-also-true-for-subset
  (implies (and (restricted-formulap f vars)
                (subset vars vars-prime))
           (restricted-formulap f vars-prime)))
)

;; (DEFTHM cone-of-influence-reduction-is-sound
;;   (implies (and (restricted-formulap f (cone-variables vars C))
;;                 (circuitp C))
;;            (equal (ltl-semantics f
;;                                  (create-kripke (cone-of-influence-reduction C
;;                                                                              vars)))
;;                   (ltl-semantics f (create-kripke C))))
;;   :hints (("Goal"
;;            :in-theory (disable restricted-formulap 
;;                                circuit-bisim-implies-same-ltl-semantics)
;;            :use ((:instance circuit-bisim-implies-same-ltl-semantics
;;                             (n (create-kripke (cone-of-influence-reduction C
;;                                                                            vars)))
;;                             (m (create-kripke C))
;;                             (vars (cone-variables vars C)))))))

;; ;; So we are done. Let us prove a couple of handy theorems.

;; (DEFTHM cone-of-influence-reduction-is-sound-generalized
;;   (implies (and (subset interesting-vars (cone-variables vars C))
;;                 (circuitp C)
;;                 (restricted-formulap f interesting-vars))
;;            (equal (ltl-semantics f (create-kripke 
;;                                     (cone-of-influence-reduction C vars)))
;;                   (ltl-semantics f (create-kripke C)))))


;; The following two theorems were non-locally stated on Sat Nov 8
;; 14:25:28 2008 (after commenting out the above).  These are the
;; theorems about cone of influence reduction that justify the
;; bisimulation.

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




                