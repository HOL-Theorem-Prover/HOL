(in-package "ACL2")

#|
  
  circuit-bisim.lisp
  ~~~~~~~~~~~~~~~~~~

In this book, we define a specific bisimilarity relation
evaluation-eq. Roughly, two "circuit states" are evaluation-eq if they match on
a specific collection of variables. We prove that evaluation-eq is a
bisimilarity relation. In a later book, we will prove that this bisimilarity
relation holds between the "Kripke Structure of a circuit" and the "Kripke
Structure of the cone of influence of the circuit". That will enable us to
prove that the two kripke structures satisfy the same LTL formula when
restricted by vars.

|#

(include-book "ltl")

(in-theory (disable subset-of-empty-is-empty
                    subset-of-nil-is-nil))

(in-theory (enable subset set-intersect))

(defun evaluation-eq (p q vars)
  (if (endp vars) T
    (and (equal (<- p (first vars))
                (<- q (first vars)))
         (evaluation-eq p q (rest vars)))))

;; We prove evaluation-eq is symmetric here, but I dont want to deal with loop
;; stoppers so we prove it only for the purpose of use hints.

(defthm evaluation-eq-is-symmetric
  (equal (evaluation-eq p q vars)
         (evaluation-eq q p vars))
  :rule-classes nil)

(defun evaluation-eq-member-p (st states vars)
  (if (endp states) nil
    (if (evaluation-eq st (first states) vars) T
      (evaluation-eq-member-p st (rest states) vars))))

(defun evaluation-eq-member (st states vars)
  (if (endp states) nil
    (if (evaluation-eq st (first states) vars)
        (first states)
      (evaluation-eq-member st (rest states) vars))))

(defthm member-is-memberp
  (implies (evaluation-eq-member-p p states vars)
           (memberp (evaluation-eq-member p states vars) 
                    states)))

(defthm member-is-evaluation-eq
  (implies (evaluation-eq-member-p p states vars)
           (evaluation-eq p (evaluation-eq-member p states vars) 
                          vars)))

(defun-sk strict-evaluation-p (st vars)
  (forall v (implies (not (memberp v vars))
                     (not (<- st v)))))

(defthm strict-evaluation-p-expanded
  (implies (and (strict-evaluation-p st vars)
                (not (memberp v vars)))
           (not (<- st v)))
  :hints (("Goal"
           :use strict-evaluation-p-necc)))

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

(defthm all-truthsp-label-expanded
  (implies (and (all-truthsp-label label s vars)
                (memberp v vars)
                (equal (<- s v) T))
           (memberp v label)))

(defun only-all-truths-p (states m vars) 
  (if (endp states) T
    (and (all-truthsp-label (label-of (first states) m) (first states) vars)
         (only-all-truths-p (rest states) m vars))))

(defun label-subset-vars (states m vars)
  (if (endp states) T
    (and (subset (label-of (first states) m) vars)
         (label-subset-vars (rest states) m vars))))

(defthm label-subset-subset-reduction
  (implies (and (label-subset-vars states m vars)
                (memberp p states))
           (subset (label-of p m) vars)))

;; Now for a few properties governing the next state.

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

(defthm well-formed-transition-p-expanded
  (implies (and (well-formed-transition-p states-m trans-m states-n trans-n vars)
                (evaluation-eq p q vars)
                (evaluation-p p vars)
                (memberp p states-m)
                (memberp q states-n)
                (evaluation-p q vars))
           (evaluation-eq-subset-p (<- trans-m p) (<- trans-n q) vars))
  :hints (("Goal"
           :use well-formed-transition-p-necc)))

(in-theory (disable well-formed-transition-p well-formed-transition-p-necc))


(defun transition-subset-p (states states-prime trans)
  (if (endp states) T
    (and (subset (<- trans (first states)) states-prime)
         (transition-subset-p (rest states) states-prime trans))))

(defthm transition-subset-p-expanded
  (implies (and (transition-subset-p states states-prime trans)
                 (memberp p states)
                 (memberp r (<- trans p)))
            (memberp r states-prime)))


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


;; Now that we have defined a bisimilar relation between circuit models, let us
;; prove that this is actually a bisimilar relation.

;; So what do we need to have? Given two circuit models m and m', we need to
;; show that the bisimilarity witness from m to m' and from m' to m.

(defun c-bisimilar-initial-state-witness-m->n (s m n vars)
  (declare (ignore m))
  (evaluation-eq-member s (initial-states n) vars))

(defun c-bisimilar-initial-state-witness-n->m (m s n vars)
  (declare (ignore n))
  (evaluation-eq-member s (initial-states m) vars))

(defthm all-evaluations-considers-an-evaluation-a-member
  (implies (and (evaluation-p st vars)
                (all-evaluations-p states vars))
           (evaluation-eq-member-p st states vars))
  :hints (("Goal"
           :use all-evaluations-p-necc)))

(in-theory (disable all-evaluations-p all-evaluations-p-necc))


(local
(defthm c-bisimilar-equiv-implies-init->init-n->m
  (implies (and (c-bisim-equiv m n vars)
                (memberp s (initial-states n)))
           (memberp (c-bisimilar-initial-state-witness-n->m m s n vars)
                    (initial-states m))))
)

(local
(defthm c-bisimilar-equiv-implies-init->init-m->n
  (implies (and (c-bisim-equiv m n vars)
                (memberp s (initial-states m)))
           (memberp (c-bisimilar-initial-state-witness-m->n s m n vars)
                    (initial-states n))))
)

(local
(defthm subset-transitive-member
  (implies (and (memberp s init)
		(subset init states))
	   (memberp s states)))
)

(local
(defthm c-bisimilar-equiv-implies-bisimilar-initial-states-m->n
   (implies (and (c-bisim-equiv m n vars)
                 (memberp s (initial-states m)))
            (circuit-bisim s m 
                           (c-bisimilar-initial-state-witness-m->n s m n vars) 
                           n vars))
   :otf-flg t
   :hints (("Goal"
            :do-not '(generalize eliminate-destructors)
            :do-not-induct t
	    :in-theory (disable member-is-memberp 
				evaluation-eq-subset-to-member)
	    :use ((:instance evaluation-eq-subset-to-member
			     (p s)
			     (m-states (initial-states m))
			     (n-states (initial-states n)))
		  (:instance member-is-memberp
			     (p s)
			     (states (initial-states n)))))))
)

(local
(defthm c-bisimilar-equiv-implies-bisimilar-initial-states-n->m
   (implies (and (c-bisim-equiv m n vars)
                 (memberp s (initial-states n)))
            (circuit-bisim (c-bisimilar-initial-state-witness-n->m m s n vars) 
                           m s n vars))
   :otf-flg t
   :hints (("Goal"
            :do-not '(generalize eliminate-destructors)
            :do-not-induct t
	    :in-theory (disable member-is-memberp 
				evaluation-eq-subset-to-member)
	    :use ((:instance evaluation-eq-subset-to-member
			     (p s)
			     (m-states (initial-states n))
			     (n-states (initial-states m)))
		  (:instance member-is-memberp
			     (p s)
			     (states (initial-states m)))
                  (:instance 
                   evaluation-eq-is-symmetric
                   (p (evaluation-eq-member s (initial-states m) vars))
                   (q s))))))
)
                             

;; Now we go to our first difficult proof, showing that bisimilar
;; states have equal labels.

;; (label-of s m) are only truths.

(defthm truthp-label-from-only-truthp 
  (implies (and (only-truth-p states m) 
                (memberp s states)) 
           (truthp-label (label-of s m) s)))

;; And all truths are present in the label.

(defthm all-truths-p-from-only-all-truths-p 
  (implies (and (only-all-truths-p states m vars) 
                (memberp s states)) 
           (all-truthsp-label (label-of s m) s vars))) 

;; For every variable in (and vars label) they re members of vars and label.

(defthm memberp-to-intersect-reduction
  (implies (memberp v (set-intersect x y))
           (and (memberp v x)
                (memberp v y)))
  :rule-classes :forward-chaining)

;; Since they are in vars, they must evaluate the same way in q.

(defthm evaluation-eq-vars-reduction
  (implies (and (evaluation-eq p q vars)
                (memberp v vars))
           (equal (<- p v)
                  (<- q v))))

;; Thus, variables in (label-of p m) and vars will evaluate to T in q.

(defthm variables-in-label-are-T-in-q
  (implies (and (memberp v (set-intersect label vars))
		(truthp-label label p)
		(evaluation-eq p q vars))
	   (equal (<- q v) T)))

(defthm only-truthsp-and-subset-to-subset
  (implies (and (equal (<- q v) T)
		(memberp v vars)
		(subset vars variables)
		(all-truthsp-label label q variables))
	   (memberp v label)))

(defthm truthp-label-to-subset
  (implies (and (memberp v (set-intersect lp vars))
		(truthp-label lp p)
		(evaluation-eq p q vars)
		(subset vars variables)
		(all-truthsp-label lq q variables))
	   (memberp v lq)))

;; And let us do a little trick to get ACL2 from memberp to subset


(defthm truthp-label-is-a-subset
  (implies (and (truthp-label lp p)
		(evaluation-eq p q vars)
		(subset vars variables)
		(all-truthsp-label lq q variables))
	   (subset (set-intersect lp vars)
		   lq)))

(local
(defthm subset-intersect-reduction
  (implies (and (subset lp lq)
		(subset lp vars))
	   (subset lp (set-intersect lq vars))))
)

(local
(defthm truthp-label-intersect-is-a-subset
  (implies (and (truthp-label lp p)
		(evaluation-eq p q vars)
		(subset vars variables)
		(all-truthsp-label lq q variables))
	   (subset (set-intersect lp vars)
		   (set-intersect lq vars))))
)

(local
(defthm c-bisimilar-states-have-labels-equal-aux
  (implies (circuit-bisim p m q n vars)
           (subset (set-intersect (label-of p m) vars)
		   (set-intersect (label-of q n) vars)))
  :hints (("Goal"
	   :in-theory (disable truthp-label-intersect-is-a-subset)
	   :use ((:instance truthp-label-intersect-is-a-subset
			    (lp (label-of p m))
			    (lq (label-of q n))
			    (variables (variables n)))))))
)

(local
(in-theory (enable set-equal))
)

(local
(defthm c-bisimilar-states-have-labels-equal
  (implies (circuit-bisim p m q n vars)
           (set-equal (set-intersect (label-of q n) vars)
                      (set-intersect (label-of p m) vars)))
  :hints (("Goal"
	   :in-theory (disable c-bisimilar-states-have-labels-equal-aux)
           :use ((:instance  c-bisimilar-states-have-labels-equal-aux
                             (p q)
                             (m n)
                             (n m)
                             (q p))
                 (:instance  c-bisimilar-states-have-labels-equal-aux)))
          ("Goal'''"
           :use evaluation-eq-is-symmetric)))
)	  

;; Now we start with the next states.

(defun c-bisimilar-transition-witness-m->n (p r m q n vars)
  (declare (ignore p m))
  (evaluation-eq-member r (<- (transition n) q) vars))

(defun c-bisimilar-transition-witness-n->m (p m q r n vars)
  (declare (ignore q n))
  (evaluation-eq-member r (<- (transition m) p) vars))

(defthm evaluationp-for-subset
  (implies (and (evaluation-p st variables)
                (subset vars variables))
           (evaluation-p st vars)))

(defthm evaluation-p-only-evaluations-reduction
  (implies (and (only-evaluations-p states vars)
                (memberp p states))
           (evaluation-p p vars)))

(defthm r-is-evaluation-eq-member-p
  (implies (and (evaluation-eq p q vars)
                (well-formed-transition-p states-m trans-m states-n trans-n vars)
                (memberp p states-m)
                (memberp q states-n)
                (evaluation-p p vars)
                (evaluation-p q vars)
                (memberp r (<- trans-m p)))
           (evaluation-eq-member-p r (<- trans-n q) vars))
  :hints (("Goal"
           :in-theory (disable well-formed-transition-p-expanded)
           :use well-formed-transition-p-expanded)))
           
(local
(defthm c-bisimilar-witness-member-of-states-m->n
  (implies (and (circuit-bisim p m q n vars)
                (next-statep p r m)
                (memberp r (states m)))
           (memberp (c-bisimilar-transition-witness-m->n p r m q n vars)
                    (states n)))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :in-theory (enable next-statep))
          ("Goal'"
           :in-theory (disable evaluationp-for-subset
                               r-is-evaluation-eq-member-p)
           :use ((:instance r-is-evaluation-eq-member-p
                            (states-m (states m))
                            (states-n (states n))
                            (trans-m (transition m))
                            (trans-n (transition n)))
                 (:instance evaluationp-for-subset
                            (st p)
                            (variables (variables m)))
                 (:instance evaluationp-for-subset
                            (st q)
                            (variables (variables n)))))))
)

(local
(defthm c-bisimilar-witness-member-of-states-n->m
  (implies (and (circuit-bisim p m q n vars)
                (next-statep q r n)
                (memberp r (states n)))
           (memberp (c-bisimilar-transition-witness-n->m p m q r n vars)
                    (states m)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :in-theory (enable next-statep))
          ("Goal'"
           :in-theory (disable evaluationp-for-subset
                               only-evaluations-p
                               all-evaluations-p
                               evaluation-p
                               subset 
                               r-is-evaluation-eq-member-p)
           :use ((:instance r-is-evaluation-eq-member-p
                            (states-n (states m))
                            (states-m (states n))
                            (q p)
                            (p q)
                            (trans-m (transition n))
                            (trans-n (transition m)))
                 (:instance evaluationp-for-subset
                            (st p)
                            (variables (variables m)))
                 (:instance evaluationp-for-subset
                            (st q)
                            (variables (variables n)))))
          ("Goal'''"
           :use evaluation-eq-is-symmetric)))
)

(local
(defthm c-bisimilar-witness-matches-transition-m->n
  (implies (and (circuit-bisim p m q n vars)
                (next-statep p r m))
           (next-statep q (c-bisimilar-transition-witness-m->n p r m q n vars)
                        n))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (enable next-statep))
          ("Goal'"
           :in-theory (disable evaluationp-for-subset 
                               r-is-evaluation-eq-member-p)
           :use ((:instance r-is-evaluation-eq-member-p
                            (states-m (states m))
                            (states-n (states n))
                            (trans-m (transition m))
                            (trans-n (transition n)))
                 (:instance evaluationp-for-subset
                            (st p)
                            (variables (variables m)))
                 (:instance evaluationp-for-subset
                             (st q)
                             (variables (variables n)))))))
)

(local
(defthm c-bisimilar-witness-matches-transition-n->m
  (implies (and (circuit-bisim p m q n vars)
                (next-statep q r n))
           (next-statep p (c-bisimilar-transition-witness-n->m p m q r n vars)
                        m))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (enable next-statep))
          ("Goal'"
           :in-theory (disable evaluationp-for-subset
                               only-evaluations-p
                               all-evaluations-p
                               evaluation-p
                               subset 
                               r-is-evaluation-eq-member-p)
           :use ((:instance r-is-evaluation-eq-member-p
                            (q p)
                            (p q)
                            (states-n (states m))
                            (states-m (states n))
                            (trans-m (transition n))
                            (trans-n (transition m)))
                 (:instance evaluationp-for-subset
                            (st p)
                            (variables (variables m)))
                 (:instance evaluationp-for-subset
                            (st q)
                            (variables (variables n)))))
          ("Goal'''"
           :use evaluation-eq-is-symmetric)))
)
 
(local               
(defthm c-bisimilar-witness-produces-bisimilar-states-m->n
  (implies (and (circuit-bisim p m q n vars)
                 (next-statep p r m))
            (circuit-bisim r m
                       (c-bisimilar-transition-witness-m->n p r m q n vars)
                       n vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (enable next-statep))
          ("Goal'"
           :in-theory (disable evaluationp-for-subset 
                               r-is-evaluation-eq-member-p)
           :use ((:instance r-is-evaluation-eq-member-p
                            (states-m (states m))
                            (states-n (states n))
                            (trans-m (transition m))
                            (trans-n (transition n)))
                 (:instance evaluationp-for-subset
                            (st p)
                            (variables (variables m)))
                 (:instance evaluationp-for-subset
                             (st q)
                             (variables (variables n)))))))
)

(local
(defthm c-bisimilar-witness-produces-bisimilar-states-n->m
  (implies (and (circuit-bisim p m q n vars)
                 (next-statep q r n))
            (circuit-bisim 
             (c-bisimilar-transition-witness-n->m p m q r n vars)
             m r n vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (enable next-statep))
          ("Goal'"
           :in-theory (disable evaluationp-for-subset
                               only-evaluations-p
                               all-evaluations-p
                               evaluation-p
                               subset 
                               r-is-evaluation-eq-member-p)
           :use ((:instance r-is-evaluation-eq-member-p
                            (q p)
                            (p q)
                            (states-n (states m))
                            (states-m (states n))
                            (trans-m (transition n))
                            (trans-n (transition m)))
                 (:instance evaluationp-for-subset
                            (st p)
                            (variables (variables m)))
                 (:instance evaluationp-for-subset
                            (st q)
                            (variables (variables n)))))
          ("Subgoal 3" 
           :use evaluation-eq-is-symmetric)
          ("Subgoal 2"
           :use evaluation-eq-is-symmetric)
          ("Subgoal 1"
           :use ((:instance evaluation-eq-is-symmetric
                            (p (evaluation-eq-member r (<- (transition m) p)
                                                     vars))
                            (q r))))))
)

(local
(defthm circuit-modelp-is-modelp
  (implies (circuit-modelp m)
           (and (subset (initial-states m) (states m))
                 (consp (states m))
                 (next-states-in-states m (states m)))))
)

(local
(in-theory (disable circuit-bisim circuit-modelp c-bisim-equiv
                    c-bisimilar-initial-state-witness-m->n
                    set-equal
                    c-bisimilar-transition-witness-m->n
                    c-bisimilar-initial-state-witness-n->m
                    c-bisimilar-transition-witness-n->m))
)

;; (local
;; (include-book "bisimilarity")
;; )

;; (DEFTHM circuit-bisim-implies-same-ltl-semantics
;;   (implies (and (circuit-modelp m)
;;                 (circuit-modelp n)
;;                 (c-bisim-equiv m n vars)
;;                 (subset vars (variables m))
;;                 (subset vars (variables n))
;;                 (restricted-formulap f vars))
;;            (equal (ltl-semantics f m)
;;                   (ltl-semantics f n)))
;;   :hints (("Goal"
;;            :do-not '(eliminate-destructors generalize)
;;            :do-not-induct t
;;            :use 
;;            ((:functional-instance 
;;              bisimilar-models-have-same-ltl-semantics
;;              (bisimilar-equiv (lambda (m n vars)
;;                                 (c-bisim-equiv m n vars)))
;;              (modelp (lambda (m) (circuit-modelp m)))
;;              (bisimilar (lambda (p m q n vars)
;;                           (circuit-bisim 
;;                            p m q n vars)))
;;              (bisimilar-initial-state-witness-m->n
;;               (lambda (s m n vars)
;;                 (c-bisimilar-initial-state-witness-m->n
;;                  s m n vars)))
;;              (bisimilar-initial-state-witness-n->m
;;               (lambda (m s n vars)
;;                 (c-bisimilar-initial-state-witness-n->m
;;                  m s n vars)))
;;              (bisimilar-transition-witness-m->n
;;               (lambda (p r m q n vars)
;;                 (c-bisimilar-transition-witness-m->n
;;                  p r m q n vars)))
;;              (bisimilar-transition-witness-n->m
;;               (lambda (p m q r n vars)
;;                 (c-bisimilar-transition-witness-n->m
;;                  p m q r n vars))))))))
           

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
