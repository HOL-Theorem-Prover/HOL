(* See:
     Forster, Kunze and Roth,
     "The Weak Call-by-Value 𝜆-Calculus Is Reasonable for Both Time and Space", POPL 2020
   for inspiration
 *)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory relationTheory;

val _ = new_theory "Prelims";

(* ------------------
         Natural numbers
   ------------------ *)

Theorem size_induction:
  ∀f p. (∀x. ((∀y. f y < f x ⇒ p y) ⇒ p x)) ⇒ (∀x. p x)
Proof
  ntac 4 strip_tac >>
  `(∀y. f y < f x ⇒ p y)` suffices_by gs[] >>
  `∀n y. f y < n ⇒ p y` suffices_by metis_tac[] >>
    Induct_on `n` >> rw[]
QED

(* ----------------------------------------------------------------------
    Lists
   ---------------------------------------------------------------------- *)

Overload nth_error[inferior] = “oEL”

Theorem nth_error_lt_Some:
  ∀n H. n < LENGTH H ⇒ ∃x. nth_error n H = SOME x
Proof
  metis_tac[oEL_EQ_EL]
QED

Theorem nth_error_Some_lt:
  ∀n H x. nth_error n H = SOME x ⇒ n < LENGTH H
Proof
  metis_tac[oEL_EQ_EL]
QED

Theorem nth_error_map:
  ∀n H a f. nth_error n (MAP f H) = SOME a ⇒
            ∃b. nth_error n H = SOME b ∧ a = f b
Proof
  simp[oEL_EQ_EL, EL_MAP]
QED

Theorem map_nth_error:
  ∀n H x f. nth_error n H = SOME x ⇒ nth_error n (MAP f H) = SOME (f x)
Proof
  simp[oEL_EQ_EL, EL_MAP]
QED

Theorem nth_error_NONE_lt:
  ∀n H. nth_error n H = NONE ⇒ LENGTH H ≤ n
Proof
  metis_tac[oEL_EQ_EL, NOT_LESS_EQUAL, TypeBase.distinct_of “:'a option” ]
QED

Theorem nth_error_lt_NONE:
  ∀n H. LENGTH H ≤ n ⇒ nth_error n H = NONE
Proof
  metis_tac[oEL_EQ_EL, NOT_LESS_EQUAL, TypeBase.nchotomy_of “:'a option” ]
QED

Theorem nth_error_SOME_lemma:
  ∀n H h t x.
    nth_error n (h::t) = SOME x ⇒
    1 <= n ⇒
    nth_error (n-1) t = SOME x
Proof
  simp[oEL_EQ_EL, rich_listTheory.EL_CONS, arithmeticTheory.PRE_SUB1]
QED

Theorem nth_error_SOME_in_H:
  ∀n H x. nth_error n H = SOME x ⇒ MEM x H
Proof
  simp[MEM_EL, oEL_EQ_EL] >> metis_tac[]
QED

Theorem nth_error_In:
  ∀l n x.
    nth_error n l = SOME x ⇒ MEM x l
Proof
  metis_tac[nth_error_SOME_in_H]
QED

Theorem nth_error_app1:
  ∀l l' n. n < LENGTH l ⇒
           nth_error n (l++l') = nth_error n l
Proof
  simp[oEL_THM, EL_APPEND_EQN]
QED

Theorem nth_error_app2:
  ∀l l' n.
    LENGTH l ≤ n ⇒
    nth_error n (l++l') = nth_error (n-LENGTH l) l'
Proof
  simp[oEL_THM, EL_APPEND_EQN, AllCaseEqs(), SF CONJ_ss]
QED

(* ------------------
           Relations
   ------------------ *)

Definition reducible:
        reducible R x = ∃x'. R x x'
End

Definition functional:
        functional R = ∀x y y'. R x y ⇒ R x y' ⇒ y = y'
End

Definition stepFunction:
        stepFunction R f =
                ∀x. case (f x) of
                                SOME y => R x y
                          | NONE   => ∀y. ¬(R x y)
End

Definition computable:
        computable R = ∃f. stepFunction R f
End

(* HOL4 addition: uses Hilbert choice *)
Theorem everything_computable:
  ∀R. computable R
Proof
  rw[computable] >>
  qexists ‘λx. some y. R x y’ >> rw[stepFunction] >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp[]
QED

Inductive terminatesOn:
        ∀(R: 'a -> 'a -> bool) (x: 'a).
                (∀x'. R x x' ⇒ terminatesOn R x') ⇒ terminatesOn R x
End

(* R: stepping/reducing function *)
Inductive evaluates:
        (∀x. ¬reducible R x ⇒ evaluates R x x) ∧
        ∀x y z. R x y ∧ evaluates R y z ⇒ evaluates R x z
End

Definition normalizes:
        normalizes R x = ∃y. evaluates R x y
End

(* Fact 1.1 *)
Theorem evaluates_fun:
        ∀R. functional R ⇒ functional (evaluates R)
Proof
        rw[functional] >> pop_assum mp_tac >> qid_spec_tac `y'` >> pop_assum mp_tac >>
        MAP_EVERY qid_spec_tac [`y`, `x`] >> ho_match_mp_tac evaluates_strongind >> rw[]
        >- (gvs[Once evaluates_cases] >> gvs[reducible])
        >> pop_assum (strip_assume_tac o PURE_ONCE_REWRITE_RULE[evaluates_cases])
        >- gvs[reducible]
        >> `x' = y''` by metis_tac[] >> gvs[]
QED

(* Fact 1.2 *)
Theorem normalizes_terminates:
        functional R ⇒ (∀x. normalizes R x ⇒ terminatesOn R x)
Proof
        rw[normalizes] >> qpat_x_assum (`functional R`) mp_tac >>
        pop_assum mp_tac >> MAP_EVERY qid_spec_tac [`y`, `x`] >>
        Induct_on ‘evaluates’ >> rw[] (* 2 *)
        >- (simp[Once terminatesOn_cases] >> metis_tac[reducible]) >>
        first_x_assum drule >> rw[] >> simp[Once terminatesOn_cases] >>
        metis_tac[functional]
QED

Theorem irred_evaluates_refl:
        ∀ x. (∀y. ¬ R x y) ⇒ evaluates R x x
Proof
        metis_tac[evaluates_rules,reducible]
QED

(* Fact 1.3 *)
Theorem terminates_normalizes:
        computable R ⇒ ∀x. terminatesOn R x ⇒ normalizes R x
Proof
        rw[] >> qpat_x_assum (`computable R`) mp_tac >>
        pop_assum mp_tac >> qid_spec_tac `x` >>
        Induct_on `terminatesOn` >> rw[normalizes] >>
        ‘computable R ⇒ ∀x'.R x x' ⇒ terminatesOn R x' ∧ ∃y. evaluates R x' y’
        by metis_tac[] >>
        first_x_assum drule >> strip_tac >>
        qpat_x_assum ‘computable _’ mp_tac >> rw[computable,stepFunction] >>
        Cases_on ‘f x’ (* 2 *)
        >- (first_x_assum $ qspec_then ‘x’ assume_tac >> rfs[] >>
            metis_tac[irred_evaluates_refl]) >>
        first_x_assum $ qspec_then ‘x’ assume_tac >> rfs[] >>
        first_x_assum drule >> strip_tac >> metis_tac[evaluates_rules]
QED

Theorem evaluates_irred:
        ∀x y. evaluates R x y ⇒ ¬reducible R y
Proof
        Induct_on ‘evaluates’ >> rw[]
QED

(* ------------------
              Misc
   ------------------ *)

Definition noneHolds:
        noneHolds Ps =
                case Ps of
                        | [] => T
                        | P::Ps => ¬P ∧ noneHolds Ps
End

Definition exactlyOneHolds:
        exactlyOneHolds Ps =
                case Ps of
                        | [] => F
                        | P::Ps => (P ∧ noneHolds Ps) ∨ (¬P ∧ exactlyOneHolds Ps)
End

(* -----------------------
    Coq.Classes.Morphisms
   ----------------------- *)

Definition respectful:
  respectful R R' = (λf g. ∀x y. R x y ⇒ R' (f x) (g y))
End

(* ------------------
              Relations
   ------------------ *)

Theorem NRC_ADD_EQN_R:
  ∀R m n x z.
    (∃y. NRC R m x y ∧ NRC R n y z) ⇒ NRC R (m + n) x z
Proof
  metis_tac[NRC_ADD_EQN]
QED

Theorem NRC_add:
  ∀R n m s t.
    NRC R (n + m) s t <=> ((NRC R n) ∘ᵣ (NRC R m)) s t
Proof
  simp[O_DEF] >> metis_tac[NRC_ADD_EQN]
QED

Theorem NRC_add_L:
  ∀R n m s t.
    NRC R (n + m) s t ⇒ ((NRC R n) ∘ᵣ (NRC R m)) s t
Proof
  metis_tac[NRC_add]
QED

Theorem NRC_add_R:
  ∀R n m s t.
    ((NRC R n) ∘ᵣ (NRC R m)) s t ⇒ NRC R (n + m) s t
Proof
  metis_tac[NRC_add]
QED

Theorem NRC_1_L:
  ∀R.
   (∀x y. R x y ⇒ (NRC R 1) x y)
Proof
  metis_tac[NRC_1]
QED

Theorem NRC_1_R:
  ∀R.
   (∀x y. (NRC R 1) x y ⇒ R x y)
Proof
  metis_tac[NRC_1]
QED

(* reduce while keeping track of the maximum size of terms *)
Inductive redWithMaxSize:
[~R:]
  ∀size step (m: num) s. m = size s ⇒ redWithMaxSize size step m s s
[~C:]
  ∀size step (s: 'a) (s': 'a) (t: 'a) (m: num) (m':num).
    step s s' ∧
    redWithMaxSize size step m' s' t ∧
    m = MAX (size s) m' ⇒
    redWithMaxSize size step m s t
End

Theorem redWithMaxSize_ge:
  ∀size step s t m.
    redWithMaxSize size step m s t ⇒
    size s ≤ m ∧ size t ≤ m
Proof
  Induct_on `redWithMaxSize` >> rw[]
QED

Theorem redWithMaxSize_trans:
  ∀size step s t u m1 m2 m3.
    redWithMaxSize size step m1 s t ⇒
    redWithMaxSize size step m2 t u ⇒
    MAX m1 m2 = m3 ⇒
    redWithMaxSize size step m3 s u
Proof
  Induct_on `redWithMaxSize` >> rw[]
  >- (qpat_x_assum `redWithMaxSize _ _ _ _ _` mp_tac >>
      rw[Once redWithMaxSize_cases]
      >- rw[Once redWithMaxSize_cases]
      >> rw[Once redWithMaxSize_cases] >>
      drule redWithMaxSize_ge >> rw[] >>
      rw[Once MAX_DEF] >> fs[NOT_LESS] >> rw[]
      >- (rw[Once MAX_DEF] >>
          goal_assum drule >> goal_assum drule >>
          rw[MAX_DEF])
      >> metis_tac[MAX_DEF])
  >> rw[Once redWithMaxSize_cases] >>
  drule redWithMaxSize_ge >> rw[] >>
  `size s' ≤ m1'` by metis_tac[redWithMaxSize_ge] >>
  `size t ≤ m1'` by metis_tac[redWithMaxSize_ge] >>
  first_x_assum drule >> rw[] >>
  pop_assum mp_tac >> rw[Once redWithMaxSize_cases]
  >- (pop_assum mp_tac >> rw[Once MAX_DEF] >>
      fs[NOT_LESS] >>
      drule_all LESS_EQUAL_ANTISYM >>
      qpat_x_assum `size s' ≤ m2` (fn _ => all_tac) >>
      qpat_x_assum `m2 ≤ size s'` (fn _ => all_tac) >>
      rw[] >>
      `∃s'' m'.
        step s s'' ∧ redWithMaxSize size step m' s'' s' ∧
        MAX (MAX (size s) (size s')) (size s') = MAX (size s) m'` suffices_by simp[] >>
      qexistsl_tac [`s'`, `size s'`] >> rw[]
      >- rw[Once redWithMaxSize_cases]
      >> rw[Once MAX_DEF])
  >> `∃s' m'.
        step s s' ∧ redWithMaxSize size step m' s' u ∧
        MAX (MAX (size s) m1') m2 = MAX (size s) m'` suffices_by simp[] >>
  qexistsl_tac [`s'`, `MAX m1' m2`] >> rw[]
  >- (rw[Once redWithMaxSize_cases] >> metis_tac[])
  >> `MAX (MAX (size s) m1') m2 = MAX (size s) (MAX m1' m2)` suffices_by simp[] >>
  rw[MAX_ASSOC]
QED

val _ = export_theory ()
