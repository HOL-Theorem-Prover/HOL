(in-package "ACL2")

; Fix path when including present file in inputs/ directory:
(include-book "summary")

(encapsulate
 ()

 (local
  (defthm range-transition-relation-lemma
    (implies (and (memberp p states)
                  (memberp q (<- transition p))
                  (transition-subset-p states
                                       states-prime
                                       transition))
             (memberp q states-prime))))

 (defthm range-transition-relation
   (implies (and (memberp p (g :states M)) ; sadly, seems necessary
                 (next-statep p q M)
                 (circuit-modelp M))
            (memberp q (g :states M)))))

; MODEL M /\ (|= memberp s0 (S0 M)) ==> (|= memberp s0 (S M))

(defthm subset-implies-memberp
  (implies (and (subset x y)
                (memberp a x))
           (memberp a y)))

(defthm initial-state-is-state
  (implies (and (circuit-modelp M)
                (memberp s0 (g :initial-states M)))
           (memberp s0 (g :states M))))

; Some set-theoretic lemmas:

(defthm memberp-set-union
  (equal (memberp a (set-union x y))
         (or (memberp a x)
             (memberp a y))))

(defthm memberp-set-intersect
  (equal (memberp a (set-intersect x y))
         (and (memberp a x)
              (memberp a y))))

(defthm subset-preserves-memberp
  (implies (and (subset x y)
                (memberp a x))
           (equal (memberp a y)
                  t)))

(defthm set-equal-implies-equal-memberp
  (implies (set-equal x y)
           (equal (equal (memberp a x)
                         (memberp a y))
                  t))
  :hints (("Goal" :cases ((memberp a x)))))

(defthm bisim-lemma-1-lemma
  (implies (circuit-bisim p m q n vars)
           (equal (memberp a (set-intersect (label-of p m) vars))
                  (memberp a (set-intersect (label-of q n) vars))))
  :hints (("Goal"
           :in-theory
           (disable circuit-bisim memberp label-of set-equal
                    c-bisimilar-states-have-labels-equal
                    set-equal-implies-equal-memberp)
           :use (c-bisimilar-states-have-labels-equal
                 (:instance set-equal-implies-equal-memberp
                            (x (set-intersect (label-of p m) vars))
                            (y (set-intersect (label-of q n) vars)))
                 (:instance set-equal-implies-equal-memberp
                            (y (set-intersect (label-of p m) vars))
                            (x (set-intersect (label-of q n) vars))))))
  :rule-classes nil)

(defthm bisim-lemma-1
  (implies (and (memberp a vars)
                (circuit-bisim p m q n vars))
           (equal (memberp a (label-of p m))
                  (memberp a (label-of q n))))
  :hints (("Goal" :use bisim-lemma-1-lemma)))

