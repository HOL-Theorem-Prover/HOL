(*---------------------------------------------------------------------------*)
(* Simple polynomial evaluator example                                       *)
(*---------------------------------------------------------------------------*)

use "translator.sml";

open bossLib arithmeticTheory  pairTheory combinTheory optionTheory listTheory;

Definition polyp_def:
 polyp [] = T /\
 polyp ((c,e)::r) =
     (polyp r /\ c <> 0 /\ 0 <= e /\
      (NULL r \/ SND(HD r) < e))
End

Definition eval_poly_def:
 eval_poly [] v = 0 ∧
 eval_poly ((c,e)::r) v = c * (v ** e) + eval_poly r v
End

Definition sum_polys_def:
 sum_polys [] [] = [] ∧
 sum_polys [] p = p ∧
 sum_polys p [] = p ∧
 sum_polys ((c1,e1)::r1) ((c2,e2)::r2) =
     if e1 = e2 then
        (c1+c2,e1) :: sum_polys r1 r2 else
     if e1 < e2 then
       (c2,e2)::sum_polys ((c1,e1)::r1) r2
     else
       (c1,e1)::sum_polys r1 ((c2,e2)::r2)
End

Theorem cond_thm:
  (!x y:'a. (if T then x else y) = x) /\
  (!x y:'a. (if F then x else y) = y)
Proof
  rw[]
QED

Definition COMMA_def:
  COMMA x y = (x,y)
End

Theorem null_thm:
  (NULL ([]:'a list) = T) /\ (!h t. NULL(h::t : 'a list) = F)
Proof
rw[]
QED

Theorem suc_thm:
  ∀m. SUC m = 1 + m
Proof
  decide_tac
QED

Theorem leq_thm:
  !x y. x <= y <=> x < y \/ x = y
Proof
  rw[]
QED

val basis_defs =
  [cond_thm, COMMA_def, HD, null_thm, suc_thm, leq_thm, FST, SND,
   EXP, polyp_def, eval_poly_def, sum_polys_def];

val goals =
   [mk_named_goal "eval_sum_poly_distrib"
     ``∀x y v.
         polyp x ∧ polyp y ⇒
           eval_poly (sum_polys x y) v
           =
           eval_poly x v + eval_poly y v``];

val sexps = map hol_sexp (basis_defs @ goals);

(*
val basis_defs =
   [⊢ (∀x y. (if T then x else y) = x) ∧ ∀x y. (if F then x else y) = y,
    ⊢ ∀x y. COMMA x y = (x,y),
    ⊢ ∀h t. HD (h::t) = h,
    ⊢ (NULL [] ⇔ T) ∧ ∀h t. NULL (h::t) ⇔ F,
    ⊢ ∀m. SUC m = 1 + m,
    ⊢ ∀x y. x ≤ y ⇔ x < y ∨ x = y,
    ⊢ ∀x y. FST (x,y) = x,
    ⊢ ∀x y. SND (x,y) = y,
    ⊢ (∀m. m ** 0 = 1) ∧ ∀m n. m ** SUC n = m * m ** n,
    ⊢ (polyp [] ⇔ T) ∧
      ∀r e c.
        polyp ((c,e)::r) ⇔
        polyp r ∧ c ≠ 0 ∧ 0 ≤ e ∧ (NULL r ∨ SND (HD r) < e),
    ⊢ (∀v. eval_poly [] v = 0) ∧
      ∀v r e c. eval_poly ((c,e)::r) v = c * v ** e + eval_poly r v,
    ⊢ sum_polys [] [] = [] ∧ (∀v7 v6. sum_polys [] (v6::v7) = v6::v7) ∧
      (∀v3 v2. sum_polys (v2::v3) [] = v2::v3) ∧
      ∀r2 r1 e2 e1 c2 c1.
        sum_polys ((c1,e1)::r1) ((c2,e2)::r2) =
        if e1 = e2 then (c1 + c2,e1)::sum_polys r1 r2
        else if e1 < e2 then (c2,e2)::sum_polys ((c1,e1)::r1) r2
        else (c1,e1)::sum_polys r1 ((c2,e2)::r2)]: thm list

val sexps =
   [("COND",
     (defhol
        :fns ((cond (:arrow* :bool a a a)))
        :defs ((:forall ((x a) (y a))
           (equal (hap* (cond (typ (:arrow* :bool a a a))) (hp-true) x y) x))
          (:forall ((x a) (y a))
           (equal (hap* (cond (typ (:arrow* :bool a a a))) (hp-false) x y) y))))),
    ("COMMA",
     (defhol
        :fns ((comma (:arrow* a b (:hash a b))))
        :defs ((:forall ((x a) (y b))
           (equal (hap* (comma (typ (:arrow* a b (:hash a b)))) x y)
            (hp-comma x y)))))),
    ("HD",
     (defhol
        :fns ((hd (:arrow* (:list a) a)))
        :defs ((:forall ((h a) (t (:list a)))
           (equal (hap* (hd (typ (:arrow* (:list a) a))) (hp-cons h t)) h))))),
    ("NULL",
     (defhol
        :fns ((null (:arrow* (:list a) :bool)))
        :defs ((equal
           (hap* (null (typ (:arrow* (:list a) :bool))) (hp-nil (typ a)))
           (hp-true))
          (:forall ((h a) (t (:list a)))
           (equal (hap* (null (typ (:arrow* (:list a) :bool))) (hp-cons h t))
            (hp-false)))))),
    ("SUC",
     (defhol
        :fns ((suc (:arrow* :num :num)))
        :defs ((:forall ((m :num))
           (equal (hap* (suc (typ (:arrow* :num :num))) m)
            (hp+ (hp-num 1) m)))))),
    ("<=",
     (defhol
        :fns ((<= (:arrow* :num :num :bool)))
        :defs ((:forall ((x :num) (y :num))
           (equal (hap* (<= (typ (:arrow* :num :num :bool))) x y)
            (hp-or (hp< x y) (hp= x y))))))),
    ("FST",
     (defhol
        :fns ((fst (:arrow* (:hash a b) a)))
        :defs ((:forall ((x a) (y b))
           (equal (hap* (fst (typ (:arrow* (:hash a b) a))) (hp-comma x y))
            x))))),
    ("SND",
     (defhol
        :fns ((snd (:arrow* (:hash a b) b)))
        :defs ((:forall ((x a) (y b))
           (equal (hap* (snd (typ (:arrow* (:hash a b) b))) (hp-comma x y))
            y))))),
    ("EXP",
     (defhol
        :fns ((exp (:arrow* :num :num :num)))
        :defs ((:forall ((m :num))
           (equal (hap* (exp (typ (:arrow* :num :num :num))) m (hp-num 0))
            (hp-num 1)))
          (:forall ((m :num) (n :num))
           (equal
            (hap* (exp (typ (:arrow* :num :num :num))) m
             (hap* (suc (typ (:arrow* :num :num))) n))
            (hp* m (hap* (exp (typ (:arrow* :num :num :num))) m n))))))),
    ("polyp",
     (defhol
        :fns ((polyp (:arrow* (:list (:hash :num :num)) :bool)))
        :defs ((equal
           (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool)))
            (hp-nil (typ (:hash :num :num)))) (hp-true))
          (:forall ((r (:list (:hash :num :num))) (e :num) (c :num))
           (equal
            (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool)))
             (hp-cons (hp-comma c e) r))
            (hp-and
             (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool))) r)
             (hp-and (hp-not (hp= c (hp-num 0)))
              (hp-and
               (hap* (<= (typ (:arrow* :num :num :bool))) (hp-num 0) e)
               (hp-or
                (hap* (null (typ (:arrow* (:list (:hash :num :num)) :bool)))
                 r)
                (hp<
                 (hap* (snd (typ (:arrow* (:hash :num :num) :num)))
                  (hap*
                   (hd
                    (typ
                     (:arrow* (:list (:hash :num :num)) (:hash :num :num))))
                   r)) e)))))))))),
    ("eval_poly",
     (defhol
        :fns ((eval_poly (:arrow* (:list (:hash :num :num)) :num :num)))
        :defs ((:forall ((v :num))
           (equal
            (hap*
             (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
             (hp-nil (typ (:hash :num :num))) v) (hp-num 0)))
          (:forall ((v :num) (r (:list (:hash :num :num))) (e :num) (c :num))
           (equal
            (hap*
             (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
             (hp-cons (hp-comma c e) r) v)
            (hp+ (hp* c (hap* (exp (typ (:arrow* :num :num :num))) v e))
             (hap*
              (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
              r v))))))),
    ("sum_polys",
     (defhol
        :fns ((sum_polys
           (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
            (:list (:hash :num :num)))))
        :defs ((equal
           (hap*
            (sum_polys
             (typ
              (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
               (:list (:hash :num :num))))) (hp-nil (typ (:hash :num :num)))
            (hp-nil (typ (:hash :num :num))))
           (hp-nil (typ (:hash :num :num))))
          (:forall ((v7 (:list (:hash :num :num))) (v6 (:hash :num :num)))
           (equal
            (hap*
             (sum_polys
              (typ
               (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                (:list (:hash :num :num))))) (hp-nil (typ (:hash :num :num)))
             (hp-cons v6 v7)) (hp-cons v6 v7)))
          (:forall ((v3 (:list (:hash :num :num))) (v2 (:hash :num :num)))
           (equal
            (hap*
             (sum_polys
              (typ
               (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                (:list (:hash :num :num))))) (hp-cons v2 v3)
             (hp-nil (typ (:hash :num :num)))) (hp-cons v2 v3)))
          (:forall
           ((r2 (:list (:hash :num :num))) (r1 (:list (:hash :num :num)))
            (e2 :num) (e1 :num) (c2 :num) (c1 :num))
           (equal
            (hap*
             (sum_polys
              (typ
               (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                (:list (:hash :num :num))))) (hp-cons (hp-comma c1 e1) r1)
             (hp-cons (hp-comma c2 e2) r2))
            (hap*
             (cond
              (typ
               (:arrow* :bool (:list (:hash :num :num))
                (:list (:hash :num :num)) (:list (:hash :num :num)))))
             (hp= e1 e2)
             (hp-cons (hp-comma (hp+ c1 c2) e1)
              (hap*
               (sum_polys
                (typ
                 (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                  (:list (:hash :num :num))))) r1 r2))
             (hap*
              (cond
               (typ
                (:arrow* :bool (:list (:hash :num :num))
                 (:list (:hash :num :num)) (:list (:hash :num :num)))))
              (hp< e1 e2)
              (hp-cons (hp-comma c2 e2)
               (hap*
                (sum_polys
                 (typ
                  (:arrow* (:list (:hash :num :num))
                   (:list (:hash :num :num)) (:list (:hash :num :num)))))
                (hp-cons (hp-comma c1 e1) r1) r2))
              (hp-cons (hp-comma c1 e1)
               (hap*
                (sum_polys
                 (typ
                  (:arrow* (:list (:hash :num :num))
                   (:list (:hash :num :num)) (:list (:hash :num :num))))) r1
                (hp-cons (hp-comma c2 e2) r2)))))))))),
    ("eval_sum_poly_distrib",
     (defhol
        :name eval_sum_poly_distrib
        :goal (:forall
          ((x (:list (:hash :num :num))) (y (:list (:hash :num :num)))
           (v :num))
          (hp-implies
           (hp-and
            (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool))) x)
            (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool))) y))
           (hp=
            (hap*
             (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
             (hap*
              (sum_polys
               (typ
                (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                 (:list (:hash :num :num))))) x y) v)
            (hp+
             (hap*
              (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
              x v)
             (hap*
              (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
              y v)))))))]: (string * t) list
*)

(* Another version, where polyp is defined with deeper pattern-matching
Definition polyp_def:
 (polyp [] = T) /\
 (polyp [(c,e)] = (0 < c /\ 0 <= e)) /\
 (polyp ((c1,e1)::(c2,e2)::r) =
      (0 < c1 /\ 0 <= e1 /\ e2 < e1 /\ polyp ((c2,e2)::r)))
End

Theorem eval_poly_sum_polys:
 ∀x y v. polyp x ∧ polyp y ⇒
           eval_poly (sum_polys x y) v
           =
           eval_poly x v + eval_poly y v
Proof
  recInduct sum_polys_ind >> rw[] >>
  gvs [eval_poly_def,sum_polys_def] >>
  subgoal `polyp r1 /\ polyp r2`
    >- (`(r1 = [] \/ (?c3 e3 t1. r1 = (c3,e3)::t1)) /\
         (r2 = [] \/ (?c4 e4 t2. r2 = (c4,e4)::t2))` by
            metis_tac [list_CASES, pair_CASES] >>
        gvs[polyp_def]) >>
  gvs[] >> rw[] >> gvs[] >> rw [eval_poly_def]
QED
*)
