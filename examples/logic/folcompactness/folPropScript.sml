open HolKernel Parse boolLib bossLib;

open pred_setTheory set_relationTheory
open folPrenexTheory folModelsTheory folLangTheory

val _ = new_theory "folProp";

(* ========================================================================= *)
(* Propositional logic as subsystem of FOL, leading to compactness.          *)
(* ========================================================================= *)

Definition pholds_def:
  (pholds v False ⇔ F) ∧
  (pholds v (Pred p l) ⇔ v (Pred p l)) ∧
  (pholds v (IMP p q) ⇔ (pholds v p ⇒ pholds v q)) ∧
  (pholds v (FALL x p) ⇔ v (FALL x p))
End

Theorem PHOLDS[simp]:
  (pholds v False ⇔ F) ∧
  (pholds v True ⇔ T) ∧
  (pholds v (Pred pnm l) ⇔ v (Pred pnm l)) ∧
  (pholds v (Not q) ⇔ ¬pholds v q) ∧
  (pholds v (Or p q) ⇔ pholds v p ∨ pholds v q) ∧
  (pholds v (And p q) ⇔ pholds v p ∧ pholds v q) ∧
  (pholds v (Iff p q) ⇔ (pholds v p ⇔ pholds v q)) ∧
  (pholds v (IMP p q) ⇔ (pholds v p ⇒ pholds v q)) ∧
  (pholds v (Exists x p) ⇔ ¬v (FALL x (Not p))) ∧
  (pholds v (FALL x p) ⇔ v (FALL x p))
Proof
  simp[pholds_def, Or_def, Not_def, Iff_def, And_def, Exists_def, True_def] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Propositional satisfaction.                                               *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "psatisfies" (Infix(NONASSOC, 450))

Definition psatisfies_def:
  v psatisfies s ⇔ ∀p. p ∈ s ⇒ pholds v p
End

Definition psatisfiable_def:
  psatisfiable s ⇔ ∃v. v psatisfies s
End

Theorem psatisfiable_mono:
  psatisfiable a ∧ b ⊆ a ⇒ psatisfiable b
Proof
  simp[psatisfiable_def, psatisfies_def, SUBSET_DEF] >> metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Extensibility of finitely satisfiable set.                                *)
(* ------------------------------------------------------------------------- *)

Definition finsat_def:
  finsat a ⇔ ∀b. b ⊆ a ∧ FINITE b ⇒ psatisfiable b
End

Theorem finsat_mono:
  finsat a ∧ b ⊆ a ⇒ finsat b
Proof
  simp[finsat_def, SUBSET_DEF]
QED

Theorem satisfiable_finsat:
  psatisfiable s ⇒ finsat s
Proof
  rw[finsat_def] >> metis_tac[psatisfiable_mono]
QED

Theorem IN_UNCURRY:
  x IN UNCURRY f ⇔ UNCURRY f x
Proof
  simp[IN_DEF]
QED

(* uses Zorn's Lemma *)
Theorem FINSAT_MAX:
  finsat a ⇒ ∃b. a ⊆ b ∧ finsat b ∧ ∀c. b ⊆ c ∧ finsat c ⇒ c = b
Proof
  strip_tac >>
  qspecl_then [‘λ(b,c). a ⊆ b ∧ b ⊆ c ∧ finsat c’,
               ‘{ b | a ⊆ b ∧ finsat b}’] mp_tac
    zorns_lemma >>
  impl_tac
  >- (rw[]
      >- (rw[EXTENSION] >> metis_tac[SUBSET_REFL] (* set is nonempty *))
      >- ((* subset is a partial order *)
          simp[partial_order_def, domain_def, range_def, transitive_def,
               antisym_def, reflexive_def, IN_UNCURRY] >> rw[]
          >- (simp[Once SUBSET_DEF, PULL_EXISTS] >> metis_tac[finsat_mono])
          >- (simp[Once SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_TRANS])
          >- metis_tac[SUBSET_TRANS]
          >- metis_tac[SUBSET_ANTISYM])
      >- ((* upper bounds of chain t *)
          rename [‘chain t _’, ‘upper_bounds t _ ≠ ∅’] >>
          fs[chain_def, upper_bounds_def, IN_UNCURRY, range_def, EXTENSION] >>
          Cases_on ‘t = ∅’ >> simp[]
          >- (ntac 2 (qexists_tac ‘a’) >> simp[]) >> fs[EXTENSION] >>
          qexists_tac ‘BIGUNION t’ >> simp[] >>
          ‘∀b. FINITE b ∧ b ⊆ BIGUNION t ⇒ ∃U. U ∈ t ∧ b ⊆ U’
             by (Induct_on ‘FINITE’ >> simp[] >> conj_tac >- metis_tac[] >>
                 rw[] >> fs[] >>
                 rename [‘b ⊆ BIGUNION chn’, ‘e ∉ b’, ‘e ∈ s1’, ‘s1 ∈ chn’,
                         ‘b ⊆ s2’, ‘s2 ∈ chn’] >>
                 ‘s1 ⊆ s2 ∨ s2 ⊆ s1’ by metis_tac[]
                 >- (qexists_tac‘s2’ >> metis_tac[SUBSET_DEF]) >>
                 qexists_tac‘s1’ >> metis_tac[SUBSET_TRANS]) >>
          ‘finsat (BIGUNION t)’
             by (simp[finsat_def] >> rw[] >>
                 first_x_assum
                   (drule_all_then (qx_choose_then ‘U’ strip_assume_tac)) >>
                 metis_tac[finsat_def]) >>
          simp[] >> metis_tac[SUBSET_BIGUNION_I])) >>
  simp[maximal_elements_def, IN_UNCURRY] >> metis_tac[SUBSET_TRANS]
QED

(* ------------------------------------------------------------------------- *)
(* Compactness.                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem finsat_extend:
  finsat b ⇒ ∀p. finsat (p INSERT b) ∨ finsat (Not p INSERT b)
Proof
  simp[finsat_def] >> strip_tac >> CCONTR_TAC >> fs[] >>
  rename [‘pos ⊆ p INSERT b’, ‘neg ⊆ Not p INSERT b’] >>
  ‘p ∉ b ∧ Not p ∉ b’ by metis_tac[ABSORPTION] >>
  ‘p ∈ pos ∧ Not p ∈ neg’ by (fs[SUBSET_DEF] >> metis_tac[]) >>
  qabbrev_tac ‘big = (pos DELETE p) ∪ (neg DELETE Not p)’ >>
  ‘big ⊆ b’ by (fs[SUBSET_DEF, Abbr‘big’] >> metis_tac[]) >>
  ‘FINITE big’ by simp[Abbr‘big’] >> ‘psatisfiable big’ by metis_tac[] >>
  ‘∃v. v psatisfies big’ by metis_tac[psatisfiable_def] >>
  ‘pholds v p ∨ pholds v (Not p)’ by simp[]
  >- (‘v psatisfies (p INSERT big)’ by fs[psatisfies_def, DISJ_IMP_THM] >>
      ‘v psatisfies pos’
        by (fs[Abbr‘big’, SUBSET_DEF, psatisfies_def] >> metis_tac[]) >>
      metis_tac[psatisfiable_def])
  >- (‘v psatisfies (Not p INSERT big)’ by fs[psatisfies_def, DISJ_IMP_THM] >>
      ‘v psatisfies neg’
        by (fs[Abbr‘big’, SUBSET_DEF, psatisfies_def] >> metis_tac[]) >>
      metis_tac[psatisfiable_def])
QED

Theorem finsat_max_complete:
  finsat b ∧ (∀c. b ⊆ c ∧ finsat c ⇒ c = b) ⇒ ∀p. p ∈ b ∨ Not p ∈ b
Proof
  rpt strip_tac >> drule_then strip_assume_tac finsat_extend >>
  metis_tac[IN_INSERT, SUBSET_DEF, ABSORPTION]
QED

Theorem finsat_max_complete_strong:
  finsat b ∧ (∀c. b ⊆ c ∧ finsat c ⇒ c = b) ⇒ ∀p. Not p ∈ b ⇔ p ∉ b
Proof
  rpt strip_tac >> reverse (Cases_on ‘p ∈ b’) >> simp[]
  >- metis_tac[finsat_max_complete] >>
  strip_tac >>
  ‘{p ; Not p} ⊆ b ∧ FINITE {p ; Not p}’ by simp[SUBSET_DEF] >>
  ‘psatisfiable {p; Not p}’ by metis_tac[finsat_def] >>
  fs[psatisfiable_def, psatisfies_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem finsat_deduction:
  finsat b ∧ (∀c. b ⊆ c ∧ finsat c ⇒ c = b) ⇒
  ∀p. p ∈ b ⇔ ∃a. FINITE a ∧ a ⊆ b ∧ ∀v. (∀q. q ∈ a ⇒ pholds v q) ⇒ pholds v p
Proof
  rpt strip_tac >> eq_tac
  >- (strip_tac >> qexists_tac ‘{p}’ >> simp[SUBSET_DEF]) >>
  strip_tac >> CCONTR_TAC >>
  drule_all_then (strip_assume_tac o GSYM) finsat_max_complete_strong >>
  fs[] >>
  ‘FINITE (Not p INSERT a) ∧ Not p INSERT a ⊆ b’ by simp[SUBSET_DEF] >>
  ‘psatisfiable (Not p INSERT a)’ by metis_tac[finsat_def] >>
  fs[psatisfiable_def, psatisfies_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac[]
QED

Theorem finsat_consistent:
  finsat b ⇒ False ∉ b
Proof
  simp[finsat_def, psatisfiable_def, psatisfies_def] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘{False}’ mp_tac) >> simp[]
QED

Theorem finsat_max_homo:
  finsat b ∧ (∀c. b ⊆ c ∧ finsat c ⇒ c = b) ⇒
  ∀p q. IMP p q ∈ b ⇔ p ∈ b ⇒ q ∈ b
Proof
  rpt strip_tac >> eq_tac
  >- (drule_all_then (rewrite_tac o Portable.single) finsat_deduction >>
      simp[] >> disch_then (qx_choose_then ‘A1’ strip_assume_tac) >>
      disch_then (qx_choose_then ‘A2’ strip_assume_tac) >>
      qexists_tac ‘A1 ∪ A2’ >> simp[]) >>
  CONV_TAC(LAND_CONV (REWR_CONV (DECIDE “p ⇒ q ⇔ ~p ∨ q”))) >>
  drule_all_then (rewrite_tac o Portable.single o GSYM)
    finsat_max_complete_strong >>
  drule_all_then (rewrite_tac o Portable.single) finsat_deduction >> simp[] >>
  disch_then (DISJ_CASES_THEN (qx_choose_then ‘A’ strip_assume_tac)) >>
  qexists_tac ‘A’ >> simp[]
QED

Theorem COMPACT_PROP:
  (∀b. FINITE b ∧ b ⊆ a ⇒ ∃v. ∀r. r ∈ b ⇒ pholds v r) ⇒
  ∃v. ∀r. r ∈ a ⇒ pholds v r
Proof
  strip_tac >>
  ‘finsat a’ by metis_tac[finsat_def, psatisfies_def, psatisfiable_def] >>
  drule_then (qx_choose_then ‘B’ strip_assume_tac) FINSAT_MAX >>
  qexists_tac ‘λp. p ∈ B’ >>
  ‘∀r. pholds (λp. p ∈ B) r ⇔ r ∈ B’ suffices_by metis_tac[SUBSET_DEF] >>
  Induct >> simp[finsat_consistent, finsat_max_homo]
QED

Theorem compact_finsat:
  psatisfiable a ⇔ finsat a
Proof
  eq_tac >- (simp[finsat_def] >> metis_tac[psatisfiable_mono]) >>
  simp[finsat_def, psatisfiable_def, psatisfies_def] >>
  metis_tac[COMPACT_PROP]
QED

(* ------------------------------------------------------------------------- *)
(* Important variant used in proving Uniformity for FOL.                     *)
(* ------------------------------------------------------------------------- *)

Theorem COMPACT_PROP_ALT:
  ∀a. (∀v. ∃p. p ∈ a ∧ pholds v p) ⇒
      ∃b. FINITE b ∧ b ⊆ a ∧ ∀v. ∃p. p ∈ b ∧ pholds v p
Proof
  rpt strip_tac >>
  Q.SUBGOAL_THEN ‘¬(∃v. ∀r. r ∈ { Not q | q ∈ a } ⇒ pholds v r)’ MP_TAC
    >- simp[PULL_EXISTS] >>
  disch_then (mp_tac o
              MATCH_MP (GEN_ALL (CONV_RULE CONTRAPOS_CONV COMPACT_PROP))) >>
  simp[] >>
  disch_then (qx_choose_then ‘b’ strip_assume_tac) >>
  qexists_tac ‘{ p | Not p ∈ b}’ >> simp[] >> rpt conj_tac
  >- (‘IMAGE Not {p | Not p ∈ b} ⊆ b’ by simp[SUBSET_DEF, PULL_EXISTS] >>
      ‘FINITE (IMAGE Not {p | Not p ∈ b})’ by metis_tac[SUBSET_FINITE] >>
      fs[INJECTIVE_IMAGE_FINITE])
  >- (fs[SUBSET_DEF] >> rw[] >> res_tac >> fs[]) >>
  fs[SUBSET_DEF] >> qx_gen_tac ‘v’ >>
  pop_assum (qspec_then ‘v’ (qx_choose_then ‘ϕ’ strip_assume_tac)) >>
  first_x_assum drule >> simp[PULL_EXISTS] >> rw[] >> fs[] >> metis_tac[]
QED

Theorem FINITE_DISJ_lemma:
  ∀a. FINITE a ⇒
      ∃ps. EVERY (λp. p ∈ a) ps ∧
           ∀v. pholds v (FOLDR Or False ps) ⇔
               ∃p. p ∈ a ∧ pholds v p
Proof
  Induct_on ‘FINITE’ >> simp[] >> rw[] >>
  rename [‘p ∉ a’, ‘EVERY _ ps’]  >> qexists_tac ‘p::ps’ >>
  dsimp[] >> irule listTheory.MONO_EVERY >> qexists_tac ‘λp. p ∈ a’ >>
  simp[]
QED

Theorem COMPACT_DISJ:
  ∀a. (∀v. ∃p. p ∈ a ∧ pholds v p) ⇒
      ∃ps. EVERY (λp. p ∈ a) ps ∧ ∀v. pholds v (FOLDR Or False ps)
Proof
  rw[] >>
  drule_then (qx_choose_then ‘b’ strip_assume_tac) COMPACT_PROP_ALT >>
  drule_then (qx_choose_then ‘ps’ strip_assume_tac) FINITE_DISJ_lemma >>
  qexists_tac ‘ps’ >> simp[] >> irule listTheory.MONO_EVERY >>
  qexists_tac ‘λp. p ∈ b’ >> fs[SUBSET_DEF]
QED

val _ = export_theory()
