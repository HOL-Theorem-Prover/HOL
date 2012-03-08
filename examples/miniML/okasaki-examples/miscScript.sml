open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib bagTheory
open relationTheory bagLib lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "misc"

val WeakLinearOrder_neg = Q.store_thm ("WeakLinearOrder_neg",
`!leq x y. WeakLinearOrder leq ⇒ (~leq x y = leq y x ∧ x ≠ y)`,
metis_tac [WeakLinearOrder, WeakOrder, trichotomous, reflexive_def,
           antisymmetric_def]);

val BAG_EVERY_DIFF = Q.store_thm ("BAG_EVERY_DIFF",
`!P b1 b2. BAG_EVERY P b1 ⇒ BAG_EVERY P (BAG_DIFF b1 b2)`,
rw [BAG_EVERY] >>
metis_tac [BAG_IN_DIFF_E]);

val BAG_EVERY_EL = Q.store_thm ("BAG_EVERY_EL",
`!P x. BAG_EVERY P (EL_BAG x) = P x`,
rw [BAG_EVERY, EL_BAG]);

val BAG_INN_BAG_DIFF = Q.store_thm ("BAG_INN_BAG_DIFF",
`!x m b1 b2. 
  BAG_INN x m (BAG_DIFF b1 b2) = 
  ∃n1 n2. (m = n1 - n2) ∧ 
          BAG_INN x n1 b1 ∧ BAG_INN x n2 b2 ∧ ~BAG_INN x (n2 + 1) b2`,
rw [BAG_INN, BAG_DIFF] >>
EQ_TAC >>
rw [] >|
[qexists_tac `b2 x + m` >>
     qexists_tac `b2 x` >>
     decide_tac,
 qexists_tac `0` >>
     qexists_tac `b2 x` >>
     decide_tac,
 decide_tac]);

val BAG_DIFF_INSERT2 = Q.store_thm ("BAG_DIFF_INSERT2",
`!x b. BAG_DIFF (BAG_INSERT x b) (EL_BAG x) = b`,
rw [BAG_DIFF, BAG_INSERT, EL_BAG, FUN_EQ_THM, EMPTY_BAG] >>
cases_on `x' = x` >>
rw []);

val _ = export_theory ();
