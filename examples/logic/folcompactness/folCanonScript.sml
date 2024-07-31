open HolKernel Parse boolLib bossLib;

open mp_then

open pred_setTheory set_relationTheory listTheory
open folSkolemTheory folPrenexTheory folModelsTheory folLangTheory
     folPropTheory

fun f $ x = f x

val _ = new_theory "folCanon";

(* ========================================================================= *)
(* Canonical models in FOL and their use to derive classic metatheorems.     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Domain of a canonical model for given language.                           *)
(* ------------------------------------------------------------------------- *)

Inductive terms:
  (∀x. terms fns (V x)) ∧
  (∀f l. (f,LENGTH l) ∈ fns ∧ (∀t. MEM t l ⇒ terms fns t) ⇒
         terms fns (Fn f l))
End

val stupid_canondom_lemma = Q.prove(
  ‘∀t. t ∈ terms (FST L) ⇒ term_functions t ⊆ FST L’,
  simp[IN_DEF] >> Induct_on ‘terms’ >>
  dsimp[SUBSET_DEF, MEM_MAP] >> metis_tac[]);

Theorem finite_subset_instance:
  ∀t'. FINITE t' ∧ t' ⊆ { formsubst v p | P v ∧ p ∈ s} ⇒
        ∃t. FINITE t ∧ t ⊆ s ∧ t' ⊆ {formsubst v p | P v ∧ p ∈ t}
Proof
  Induct_on‘FINITE’ >> simp[] >> rw[]
  >- (qexists_tac ‘∅’ >> simp[]) >> fs[] >>
  rename [‘p ∈ s’, ‘formsubst v p ∉ t'’, ‘t ⊆ s’] >>
  qexists_tac ‘p INSERT t’ >> simp[] >> conj_tac >- metis_tac[] >>
  fs[SUBSET_DEF] >>metis_tac[]
QED

Theorem finite_subset_SKOLEM:
  ∀s u. FINITE u ∧ u ⊆ { SKOLEM p | p ∈ s} ⇒
        ∃t. FINITE t ∧ t ⊆ s ∧ u = {SKOLEM p | p ∈ t}
Proof
  Induct_on ‘FINITE’ >> simp[] >> rw[]
  >- (qexists_tac ‘∅’ >> simp[]) >>
  first_x_assum (drule_then (qx_choose_then ‘tt’ strip_assume_tac)) >> rw[] >>
  rename [‘p ∈ s’] >> qexists_tac ‘p INSERT tt’ >> simp[] >>
  dsimp[EXTENSION]
QED

Theorem valuation_exists:
  ∀M. M.Dom ≠ ∅ ⇒ ∃v:num -> α. valuation M v
Proof
  simp[EXTENSION, PULL_EXISTS, valuation_def] >> qx_genl_tac [‘M’, ‘x’] >>
  strip_tac >> qexists_tac ‘K x’ >> simp[]
QED

Theorem holds_FOLDR_exists:
  ∀M xs v.
    holds M v (FOLDR Exists p xs) ⇔
    ∃as. LENGTH as = LENGTH xs ∧ EVERY M.Dom as ∧
         holds M (FOLDL (combin$C (UNCURRY UPDATE)) v (MAP2 $, xs as)) p
Proof
  Induct_on ‘xs’ >> simp[PULL_EXISTS] >> rpt gen_tac >> eq_tac
  >- (disch_then (qx_choosel_then [‘a’, ‘as’] strip_assume_tac) >>
      qexists_tac ‘a::as’ >> simp[] >> fs[IN_DEF]) >>
  simp[PULL_EXISTS] >> Cases >> simp[] >> rw[] >>
  rename [‘LENGTH as = LENGTH xs’, ‘M.Dom a’] >>
  map_every qexists_tac [‘a’, ‘as’] >> simp[] >> simp[IN_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Canonical model based on the language of a set of formulas.               *)
(* ------------------------------------------------------------------------- *)

Definition canonical_def:
  canonical L M ⇔ M.Dom = terms (FST L) ∧ ∀f. M.Fun f = Fn f
End

(* ------------------------------------------------------------------------- *)
(* Mappings between models and propositional valuations.                     *)
(* ------------------------------------------------------------------------- *)

Definition prop_of_model_def:
  prop_of_model M v (Pred p l) ⇔ holds M v (Pred p l)
End

Definition canon_of_prop_def:
  canon_of_prop L v = <| Dom := terms (FST L); Fun := Fn;
                         Pred := λp zs. v (Pred p zs) |>
End

Theorem pholds_prop_of_model:
  ∀p. qfree p ⇒ (pholds (prop_of_model M v) p ⇔ holds M v p)
Proof
  Induct >> simp[prop_of_model_def]
QED

Theorem prop_of_canon_of_prop:
  ∀p l. prop_of_model (canon_of_prop L v) V (Pred p l) = v (Pred p l)
Proof
  simp[prop_of_model_def, canon_of_prop_def] >> rpt gen_tac >>
  rpt AP_TERM_TAC >>
  qmatch_abbrev_tac ‘MAP f l = l’ >>
  ‘∀t. f t = t’ suffices_by simp[LIST_EQ_REWRITE, EL_MAP] >>
  Induct >> simp[Abbr‘f’, Cong MAP_CONG]
QED

Theorem holds_canon_of_prop:
  qfree p ⇒ (holds (canon_of_prop L v) V p ⇔ pholds v p)
Proof
  strip_tac >>
  drule_then (rewrite_tac o Portable.single o GSYM) pholds_prop_of_model >>
  Induct_on ‘p’ >> simp[prop_of_canon_of_prop]
QED

Theorem holds_canon_of_prop_general:
  qfree p ⇒ (holds (canon_of_prop L v1) v2 p ⇔ pholds v1 (formsubst v2 p))
Proof
  strip_tac >>
  drule_then (rewrite_tac o Portable.single o GSYM) pholds_prop_of_model >>
  Induct_on ‘p’ >> simp[] >>
  simp[prop_of_model_def, canon_of_prop_def] >>
  simp[Cong MAP_CONG, GSYM termsubst_termval]
QED

Theorem canonical_canon_of_prop:
  canonical L (canon_of_prop L d)
Proof
  simp[canonical_def, canon_of_prop_def]
QED

Theorem interpretation_canon_of_prop:
  ∀L d. interpretation L (canon_of_prop L d)
Proof
  simp[interpretation_def, canon_of_prop_def, pairTheory.FORALL_PROD] >>
  metis_tac[terms_rules,IN_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Equivalence theorems for tautologies.                                     *)
(* ------------------------------------------------------------------------- *)

Theorem prop_valid_imp_fol_valid:
  ∀p. qfree p ∧ (∀d. pholds d p) ⇒ ∀M v. holds M v p
Proof
  metis_tac[pholds_prop_of_model]
QED

Theorem fol_valid_imp_prop_valid:
  !p. qfree p ∧
      (∀C (v:num->term). canonical(language {p}) C ⇒ holds C v p)
       ==> !d. pholds d p
Proof
  metis_tac[canonical_canon_of_prop, holds_canon_of_prop]
QED

(* ------------------------------------------------------------------------- *)
(* Same thing for satisfiability.                                            *)
(* ------------------------------------------------------------------------- *)

Theorem satisfies_psatisfies:
  (∀p. p ∈ s ⇒ qfree p) ∧ M satisfies s ∧ valuation M v ⇒
  prop_of_model M v psatisfies s
Proof
  simp[satisfies_def, psatisfies_def] >> metis_tac[pholds_prop_of_model]
QED

Theorem psatisfies_instances:
  (∀p. p ∈ s ⇒ qfree p) ∧
  d psatisfies {formsubst v p | (∀x. v x ∈ terms (FST L)) ∧ p ∈ s} ⇒
  canon_of_prop L d satisfies s
Proof
  simp[satisfies_def, psatisfies_def, PULL_EXISTS] >> strip_tac >>
  simp[SimpL “$==>”, valuation_def, canon_of_prop_def] >> rpt strip_tac >>
  ‘pholds d (formsubst v p)’ by metis_tac[] >>
  ‘holds (canon_of_prop L d) V (formsubst v p)’
    by metis_tac[holds_canon_of_prop, qfree_formsubst] >>
  fs[holds_formsubst] >>
  ‘termval (canon_of_prop L d) V o v = v’ suffices_by (strip_tac >> fs[]) >>
  simp[FUN_EQ_THM] >> simp[termval_triv, canon_of_prop_def]
QED

Theorem satisfies_instances:
  interpretation (language t) M ⇒
  (M satisfies {formsubst i p | p ∈ s ∧ ∀x. i x ∈ terms (FST (language t))} ⇔
   M satisfies s)
Proof
  simp[satisfies_def, PULL_EXISTS] >> rpt strip_tac >> eq_tac >> rpt strip_tac
  >- metis_tac[formsubst_triv, IN_DEF, terms_rules] >>
  simp[holds_formsubst] >> first_assum irule >> simp[valuation_def] >>
  gen_tac >> irule interpretation_termval >> simp[] >>
  qexists_tac ‘predicates t’ >>
  irule interpretation_sublang >> fs[language_def] >>
  metis_tac[stupid_canondom_lemma, pairTheory.FST]
QED

(* ------------------------------------------------------------------------- *)
(* So we have compactness in a strong form.                                  *)
(* ------------------------------------------------------------------------- *)

Theorem COMPACT_CANON_QFREE:
  (∀p. p ∈ s ⇒ qfree p) ∧
  (∀t. FINITE t ∧ t ⊆ s ⇒
       ∃M. interpretation (language ss) M ∧ M.Dom ≠ ∅ ∧ M satisfies t) ⇒
  ∃C. interpretation (language ss) C ∧ canonical (language ss) C ∧
      C satisfies s
Proof
  rpt strip_tac >>
  ‘psatisfiable
     { formsubst v p | (∀x. v x ∈ terms (FST (language ss))) ∧ p ∈ s }’
    by (rewrite_tac[psatisfiable_def, psatisfies_def] >> irule COMPACT_PROP >>
        simp[GSYM psatisfies_def, GSYM psatisfiable_def] >>
        qx_gen_tac ‘u’ >> strip_tac >>
        ‘∃t. FINITE t ∧ t ⊆ s ∧
             u ⊆ {formsubst v p |
                   (∀x. v x ∈ terms (FST (language ss))) ∧ p ∈ t }’
           by (ho_match_mp_tac finite_subset_instance >> simp[]) >>
        irule psatisfiable_mono >>
        goal_assum (first_assum o mp_then Any mp_tac) >>
        first_x_assum (drule_all_then strip_assume_tac) >>
        drule_then (qx_choose_then ‘v’ strip_assume_tac) valuation_exists >>
        drule_then strip_assume_tac satisfies_instances >>
        ‘∀p. p ∈ t ⇒ qfree p’ by metis_tac[SUBSET_DEF] >>
        rewrite_tac[psatisfiable_def, psatisfies_def] >>
        qexists_tac ‘prop_of_model M v’ >> simp[GSYM psatisfies_def] >>
        irule satisfies_psatisfies >> simp[PULL_EXISTS] >>
        fs[AC CONJ_ASSOC CONJ_COMM]) >>
  fs[psatisfiable_def] >> rename [‘d psatisfies _’] >>
  qexists_tac ‘canon_of_prop (language ss) d’ >>
  simp[canonical_canon_of_prop, interpretation_canon_of_prop,
       psatisfies_instances]
QED

(* ------------------------------------------------------------------------- *)
(* Tedious lemma about sublanguage.                                          *)
(* ------------------------------------------------------------------------- *)

Theorem interpretation_restrictlanguage:
  ∀M s t. t ⊆ s ∧ interpretation (language s) M ⇒ interpretation (language t) M
Proof
  rw[language_def] >> irule interpretation_sublang >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[functions_def, SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED

Theorem interpretation_extendlanguage:
  ∀M s t. interpretation (language t) M ∧ M.Dom ≠ ∅ ∧ M satisfies t ⇒
          ∃M'. M'.Dom = M.Dom ∧ M'.Pred = M.Pred ∧
               interpretation (language s) M' ∧ M' satisfies t
Proof
  rpt strip_tac >>
  qexists_tac ‘M with Fun := λg zs. if (g,LENGTH zs) ∈ functions t then
                                      M.Fun g zs
                                    else @a. a ∈ M.Dom’ >>
  simp[] >> conj_tac
  >- (fs[interpretation_def, language_def] >> rw[] >> SELECT_ELIM_TAC >>
      fs[EXTENSION] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[satisfies_def, valuation_def] >>
  rpt strip_tac >> qmatch_abbrev_tac ‘holds M' v p’ >>
  ‘∀v. holds M v p ⇔ holds M' v p’ suffices_by metis_tac[] >>
  irule holds_functions >> simp[Abbr‘M'’] >> simp[functions_def, PULL_EXISTS] >>
  rw[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Generalize to any formulas, via Skolemization.                            *)
(* ------------------------------------------------------------------------- *)

Theorem COMPACT_LS:
  (∀t. FINITE t ∧ t ⊆ s ⇒
       ∃M. interpretation (language s) M ∧ M.Dom ≠ ∅ ∧ M satisfies t)
 ⇒
  ∃C:term model. C.Dom ≠ ∅ ∧ interpretation (language s) C ∧ C satisfies s
Proof
  strip_tac >>
  ‘∀u. FINITE u ∧ u ⊆ {SKOLEM p | p ∈ s} ⇒
       ∃M. interpretation (language {SKOLEM p | p ∈ s }) M ∧
           M.Dom ≠ ∅ ∧ M satisfies u’
    by (rpt strip_tac >>
        ‘∃t. u = {SKOLEM p | p ∈ t} ∧ FINITE t ∧ t ⊆ s’
           by metis_tac[finite_subset_SKOLEM] >> rw[] >>
        first_x_assum (drule_all_then (qx_choose_then ‘M’ strip_assume_tac))>>
        Q.SUBGOAL_THEN ‘∃M. M.Dom ≠ ∅ ∧ interpretation (language t) M ∧
                            M satisfies t’
           (qx_choose_then ‘M0’ strip_assume_tac o
            ONCE_REWRITE_RULE[SKOLEM_SATISFIABLE])
        >- (qexists_tac ‘M’ >> simp[] >>
            irule interpretation_restrictlanguage >> metis_tac[]) >>
        metis_tac[interpretation_extendlanguage]) >>
  ‘∀q. q ∈ {SKOLEM p | p ∈ s} ⇒ qfree q’ by simp[PULL_EXISTS] >>
  drule_all_then (qx_choose_then ‘CM’ strip_assume_tac) COMPACT_CANON_QFREE >>
  simp[Once SKOLEM_SATISFIABLE] >> qexists_tac ‘CM’ >> simp[] >>
  fs[canonical_def] >> simp[EXTENSION] >> simp[IN_DEF] >>
  metis_tac[terms_rules]
QED

(* ------------------------------------------------------------------------- *)
(* Split away the compactness argument.                                      *)
(* ------------------------------------------------------------------------- *)

Theorem CANON:
 ∀M:α model s.
    interpretation (language s) M ∧
    M.Dom ≠ ∅ ∧ (∀p. p IN s ⇒ qfree p) /\ M satisfies s
  ⇒
    ∃C:term model.
        C.Dom ≠ ∅ ∧ interpretation (language s) C ∧ C satisfies s
Proof
  rpt strip_tac >> irule COMPACT_LS THEN
  metis_tac[satisfies_def, SUBSET_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Conventional form of the LS theorem.                                      *)
(* ------------------------------------------------------------------------- *)

Definition LOWMOD_def:
  LOWMOD M = <| Dom := { num_of_term t | t ∈ M.Dom } ;
                Fun := λg zs. num_of_term (M.Fun g (MAP term_of_num zs)) ;
                Pred := λp zs. M.Pred p (MAP term_of_num zs) |>
End

Theorem DOM_LOWMOD_EMPTY[simp]:
  (LOWMOD M).Dom = ∅ ⇔ M.Dom = ∅
Proof
  simp[LOWMOD_def, EXTENSION]
QED

Theorem LOWMOD_termval:
  valuation (LOWMOD M) v ⇒
  ∀t. termval (LOWMOD M) v t = num_of_term (termval M (term_of_num o v) t)
Proof
  simp[SimpL “$==>”, valuation_def, LOWMOD_def] >> strip_tac >>
  Induct >> simp[Cong MAP_CONG] >- metis_tac[TERM_OF_NUM] >>
  simp[LOWMOD_def, MAP_MAP_o, Cong MAP_CONG]
QED

Theorem term_of_num_composition:
  term_of_num o v⦇ n ↦ num_of_term t ⦈ = (term_of_num o v)⦇ n ↦ t ⦈
Proof
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[]
QED


Theorem holds_LOWMOD[simp]:
  ∀p v. valuation (LOWMOD M) v ⇒
        (holds (LOWMOD M) v p ⇔ holds M (term_of_num o v) p)
Proof
  Induct >> simp[Cong MAP_CONG, LOWMOD_termval]
  >- simp[LOWMOD_def, MAP_MAP_o, Cong MAP_CONG] >>
  rw[] >> simp[LOWMOD_def, PULL_EXISTS, term_of_num_composition]
QED

Theorem interpretation_LOWMOD[simp]:
  ∀L M. interpretation L (LOWMOD M) ⇔ interpretation L M
Proof
  simp[interpretation_def, pairTheory.FORALL_PROD, LOWMOD_def] >>
  rw[EQ_IMP_THM]
  >- (rename [‘M.Fun f zs ∈ M.Dom’] >>
      first_x_assum (qspecl_then [‘f’, ‘MAP num_of_term zs’] mp_tac) >>
      simp[MEM_MAP, PULL_EXISTS, MAP_MAP_o, Cong MAP_CONG]) >>
  first_x_assum irule >> simp[MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  first_x_assum drule >> simp[PULL_EXISTS]
QED

Theorem LS:
  ∀M : α model s.
     interpretation (language s) M ∧ M.Dom ≠ ∅ ∧ (∀p. p ∈ s ⇒ qfree p) ∧
     M satisfies s
    ⇒
     ∃N: num model.
       interpretation (language s) N ∧ N.Dom ≠ ∅ ∧ N satisfies s
Proof
  rw[] >> drule_all_then strip_assume_tac CANON >>
  qexists_tac ‘LOWMOD C’ >> simp[] >>
  fs[satisfies_def] >> rw[] >> first_x_assum irule >>
  fs[valuation_def, LOWMOD_def] >> metis_tac[TERM_OF_NUM]
QED

Theorem COMPACT_LS_ALPHA:
  INFINITE 𝕌(:α) ∧
  (∀t. FINITE t ∧ t ⊆ s ⇒
       ∃M:α model.
          interpretation (language s) M ∧ M.Dom ≠ ∅ ∧ M satisfies t) ⇒
  ∃M:α model.
     interpretation (language s) M ∧ M.Dom ≠ ∅ ∧ M satisfies s
Proof
  rw[] >> drule_then (qx_choose_then ‘Cm’ strip_assume_tac) COMPACT_LS >>
  ‘∃f. INJ f 𝕌(:term) 𝕌(:α)’
    by (fs[infinite_num_inj] >> qexists_tac ‘f o num_of_term’ >>
        fs[INJ_IFF]) >>
  metis_tac[copy_models]
QED

Theorem COMPACTNESS_satisfiable:
  INFINITE 𝕌(:α) ∧ ffinsat (:α) s ⇒ satisfiable (:α) s
Proof
  rw[ffinsat_def, satisfiable_def] >>
  ‘∀t. FINITE t ∧ t ⊆ s ⇒
       ∃M. M.Dom ≠ ∅ ∧ interpretation (language s) M ∧ M satisfies t’
    by (rw[] >> first_x_assum (drule_all_then strip_assume_tac) >>
        metis_tac[interpretation_extendlanguage]) >>
  metis_tac[COMPACT_LS_ALPHA]
QED

Definition tm_constify_def[simp]:
  (tm_constify kvs (V x) = if x ∈ kvs then V x else Fn (1 ⊗ x) []) ∧
  (tm_constify kvs (Fn f zs) = Fn (0 ⊗ f) (MAP (tm_constify kvs) zs))
Termination
  WF_REL_TAC ‘measure (term_size o SND)’ >> simp[]
End

Definition varify_map_def:
  varify_map kvs m k = if k ∈ kvs then V k else m k
End

Theorem tm_constify_varify:
  tm_constify keeps t =
    termsubst (varify_map keeps (λn. Fn (1 ⊗ n) [])) (bumpterm t)
Proof
  Induct_on ‘t’ >> simp[MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG] >>
  simp[varify_map_def]
QED

Definition fm_constify_def[simp]:
  fm_constify kvs False = False ∧
  fm_constify kvs (Pred n zs) = Pred n (MAP (tm_constify kvs) zs) ∧
  fm_constify kvs (IMP p1 p2) = IMP (fm_constify kvs p1) (fm_constify kvs p2) ∧
  fm_constify kvs (FALL x p) = FALL x (fm_constify (x INSERT kvs) p)
End

Theorem FVT_tm_constify[simp]:
  ∀t. FVT (tm_constify kvs t) = kvs ∩ FVT t
Proof
  Induct >> simp[MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG]
  >- (rw[EXTENSION] >> csimp[]) >>
  simp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem FV_fm_constify[simp]:
  ∀p kvs. FV(fm_constify kvs p) = kvs ∩ FV p
Proof
  Induct >> simp[fm_constify_def, formsubst_FV, UNION_OVER_INTER]
  >- (simp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  simp[Once EXTENSION] >> csimp[] >> metis_tac[]
QED

Definition constifymod_def:
  constifymod v M = <| Dom := M.Dom ;
                       Fun := λg zs. if nfst g = 1 ∧ zs = [] then
                                       v (nsnd g)
                                     else M.Fun (nsnd g) zs ;
                       Pred := M.Pred |>
End

Theorem constifymod_rwts[simp]:
  (constifymod v M).Dom = M.Dom ∧ (constifymod v M).Pred = M.Pred
Proof
  simp[constifymod_def]
QED

Theorem termval_constify[simp]:
  termval (constifymod v M) w (tm_constify kvs t) =
  termval M (λvnm. if vnm ∈ kvs then w vnm else v vnm) t
Proof
  Induct_on ‘t’ >> simp[MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG] >>
  simp[constifymod_def] >> rw[]
QED

Theorem holds_constify:
  ∀ϕ kvs v w M.
    holds (constifymod v M) w (fm_constify kvs ϕ) ⇔
    holds M (λvnm. if vnm ∈ kvs then w vnm else v vnm) ϕ
Proof
  Induct_on ‘ϕ’ >> simp[MAP_MAP_o, combinTheory.o_DEF]
  >- asm_simp_tac (srw_ss() ++ boolSimps.ETA_ss) [] >>
  rpt gen_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC ORELSE ABS_TAC) >>
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[] >> fs[]
QED

val _ = overload_on ("FMC", “fm_constify ∅”)
Theorem holds_constify_thm[simp]:
  holds (constifymod v M) w (fm_constify ∅ ϕ) ⇔ holds M v ϕ
Proof
  simp_tac (srw_ss() ++ boolSimps.ETA_ss) [holds_constify]
QED

Theorem FMC_Not:
  FMC (Not ϕ) = Not (FMC ϕ)
Proof
  simp[Not_def]
QED

Theorem language_NOT_INSERT:
  language (Not ϕ INSERT s) = language (ϕ INSERT s)
Proof
  rw[language_def, functions_def, predicates_def] >>
  simp[Once EXTENSION, PULL_EXISTS] >> dsimp[Not_def]
QED

Theorem term_functions_tm_constify:
  term_functions (tm_constify kvs t) =
    { (0 ⊗ n, l) | (n,l) ∈ term_functions t } ∪
    { (1 ⊗ n, 0) | n ∈ FVT t ∧ n ∉ kvs }
Proof
  Induct_on ‘t’ >> simp[]
  >- (rw[] >> csimp[] >> simp[EXTENSION]) >>
  simp[MEM_MAP, PULL_EXISTS, Cong MAP_CONG, MAP_MAP_o] >>
  dsimp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem form_functions_fm_constify:
  ∀p kvs. form_functions (fm_constify kvs p) =
            { (0 ⊗ n, l) | (n,l) ∈ form_functions p } ∪
            { (1 ⊗ n, 0) | n ∈ FV p ∧ n ∉ kvs }
Proof
  Induct_on ‘p’ >>
  simp[MAP_MAP_o, MEM_MAP, combinTheory.o_DEF, PULL_EXISTS,
       term_functions_tm_constify]
  >- (dsimp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[])
  >- (simp[Once EXTENSION] >> metis_tac[]) >>
  simp[Once EXTENSION] >> metis_tac[]
QED

Theorem form_predicates_fm_constify[simp]:
  ∀p kvs. form_predicates (fm_constify kvs p) = form_predicates p
Proof
  Induct >> simp[]
QED

Theorem functions_fmc:
  functions {FMC p | p ∈ s} =
    { (0 ⊗ n,l) | (n,l) ∈ functions s } ∪
    { (1 ⊗ n,0) | n ∈ BIGUNION (IMAGE FV s) }
Proof
  dsimp[functions_def, Once EXTENSION, PULL_EXISTS,
        form_functions_fm_constify] >> metis_tac[]
QED

Theorem predicates_fmc[simp]:
  predicates {FMC p | p ∈ s } = predicates s
Proof
  simp[predicates_def, Once EXTENSION, PULL_EXISTS]
QED

Theorem valuation_constifymod[simp]:
  valuation (constifymod v M) w ⇔ valuation M w
Proof
  simp[valuation_def]
QED

Theorem constifymod_interpretation:
  valuation M v ⇒
    (interpretation (language {FMC p | p ∈ s}) (constifymod v M) ⇔
     interpretation (language s) M)
Proof
  dsimp[interpretation_def, language_def, functions_fmc, valuation_def] >>
  simp[constifymod_def] >> metis_tac[]
QED

Definition uncm_mod_def:
  uncm_mod M = <| Dom := M.Dom ;
                  Fun := λg zs. M.Fun (0 ⊗ g) zs ;
                  Pred := M.Pred |>
End

Theorem uncm_mod_rwts[simp]:
  (uncm_mod M).Dom = M.Dom ∧
  (uncm_mod M).Fun n l = M.Fun (0 ⊗ n) l ∧
  (uncm_mod M).Pred = M.Pred
Proof
  simp[uncm_mod_def]
QED

Definition uncm_map_def:
  uncm_map M fvs vnm = if vnm ∈ fvs then M.Fun (1 ⊗ vnm) []
                      else @a. a ∈ M.Dom
End

Theorem termval_uncm:
  ∀t. (FVT t DIFF kvs) ⊆ fs ⇒
      termval M v (tm_constify kvs t) =
      termval (uncm_mod M)
              (λvnm. if vnm ∈ kvs then v vnm else uncm_map M fs vnm)
              t
Proof
  Induct >> simp[] >- rw[uncm_map_def] >>
  strip_tac >> simp[MAP_MAP_o, combinTheory.o_ABS_R] >>
  ‘∀t. MEM t ts ⇒ FVT t DIFF kvs ⊆ fs’
    by (fs[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  simp[Cong MAP_CONG]
QED

Theorem UNION_DIFF_lemma:
  (s ∪ t) DIFF r = (s DIFF r) ∪ (t DIFF r)
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem holds_uncm:
  ∀ϕ v kvs fs.
     FV ϕ DIFF kvs ⊆ fs ⇒
     (holds (uncm_mod M)
            (λvnm. if vnm ∈ kvs then v vnm else uncm_map M fs vnm)
            ϕ ⇔ holds M v (fm_constify kvs ϕ))
Proof
  Induct_on ‘ϕ’ >> simp[MAP_MAP_o, combinTheory.o_DEF, UNION_DIFF_lemma]
  >- (rpt strip_tac >> rename [‘M.Pred pnm (MAP _ zs)’] >>
      ‘∀t. MEM t zs ⇒ FVT t DIFF kvs ⊆ fs’
        by (fs[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
      asm_simp_tac (srw_ss() ++ boolSimps.ETA_ss)
        [GSYM termval_uncm, Cong MAP_CONG]) >>
  rpt strip_tac >>
  ‘FV ϕ DIFF (n INSERT kvs) ⊆ fs’ by fs[SUBSET_DEF] >>
  first_x_assum (drule_then (assume_tac o GSYM)) >> simp[] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC ORELSE ABS_TAC) >>
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[] >> fs[]
QED

Theorem interpretation_uncm:
  interpretation (language {FMC p | p ∈ s}) M ⇒
  interpretation (language s) (uncm_mod M)
Proof
  simp[interpretation_def, language_def, functions_fmc, PULL_EXISTS]
QED

Theorem interpretation_uncm_valuation:
  interpretation (language {FMC p | p ∈ s}) M ∧ M.Dom ≠ ∅ ⇒
  valuation (uncm_mod M) (uncm_map M (BIGUNION (IMAGE FV s)))
Proof
  dsimp[interpretation_def, language_def, functions_fmc, PULL_EXISTS,
        valuation_def, uncm_map_def] >> rw[] >> fs[EXTENSION] >>
  SELECT_ELIM_TAC >> simp[] >> metis_tac[]
QED

Theorem entails_constify:
  entails (:α) {FMC p | p ∈ H} (FMC ϕ) ⇔ entails (:α) H ϕ
Proof
  simp[entails_def, hold_def] >>
  qmatch_abbrev_tac ‘P = Q’ >> ‘¬P ⇔ ¬Q’ suffices_by simp[] >>
  simp_tac pure_ss [NOT_FORALL_THM, Abbr‘P’, Abbr‘Q’,
                    DECIDE “¬(p ⇒ q) ⇔ p ∧ ¬q”, PULL_EXISTS, GSYM HOLDS,
                    GSYM FMC_Not] >>
  ONCE_REWRITE_TAC[GSYM language_NOT_INSERT] >>
  ONCE_REWRITE_TAC[GSYM FMC_Not] >>
  qspec_tac(‘Not ϕ’, ‘ψ’) >> qx_gen_tac ‘ϕ’ >> reverse eq_tac >> rw[]
  >- (map_every qexists_tac [‘constifymod v M’, ‘v’] >> simp[] >>
      qmatch_abbrev_tac ‘interpretation (language FML) _’ >>
      ‘FML = { FMC p | p ∈ ϕ INSERT H }’ by dsimp[EXTENSION, Abbr‘FML’] >>
      pop_assum SUBST1_TAC >> simp[constifymod_interpretation]) >>
  qabbrev_tac ‘A = ϕ INSERT H’ >>
  qabbrev_tac ‘fvs = BIGUNION (IMAGE FV A)’ >>
  ‘FV ϕ DIFF ∅ ⊆ fvs’ by simp[Abbr‘A’, Abbr‘fvs’] >>
  ‘∀p. p ∈ H ⇒ FV p DIFF ∅ ⊆ fvs’
     by (fs[Abbr‘A’, Abbr‘fvs’, SUBSET_DEF, PULL_EXISTS] >> metis_tac[]) >>
  FREEZE_THEN (fn th => fs[th])
    (holds_uncm |> SPEC_ALL |> Q.INST [‘fs’ |-> ‘fvs’, ‘kvs’ |-> ‘∅’]
                |> SIMP_RULE (srw_ss()) [] |> GSYM |> Q.GENL [‘ϕ’]) >>
  qmatch_assum_abbrev_tac ‘interpretation (language FML) _’ >>
  ‘FML = {FMC p | p ∈ A}’
     by (simp[Abbr‘FML’, Abbr‘A’, EXTENSION] >> metis_tac[]) >>
  map_every qexists_tac [‘uncm_mod M’, ‘uncm_map M fvs’] >> simp[] >>
  full_simp_tac(srw_ss() ++ boolSimps.ETA_ss)[interpretation_uncm] >>
  Q.UNABBREV_TAC ‘fvs’ >> simp[interpretation_uncm_valuation]
QED

(* but not the reverse: there might be one model that makes all the new
   constants satisfy the constraints, but then when those constants turn
   back into variables, it's by no means guaranteed that every valuation
   will satisfy the constraints *)
Theorem satisfiable_constify:
  satisfiable (:α) s ⇒ satisfiable (:α) { FMC p | p ∈ s }
Proof
  simp[satisfiable_def, satisfies_def, PULL_EXISTS] >> rpt strip_tac >>
  ‘∃d. d ∈ M.Dom’ by (fs[EXTENSION] >> metis_tac[]) >>
  ‘valuation M (K d : num -> α)’ by simp[valuation_def] >>
  qexists_tac ‘constifymod (K d) M’ >>
  simp[constifymod_interpretation]
QED

Theorem holds_FMC_ARB:
  holds M v (FMC p) ⇔ holds M ARB (FMC p)
Proof
  simp[holds_valuation]
QED


Theorem not_entails:
  ¬entails (:α) H ϕ ⇔ satisfiable (:α) { FMC p | p ∈ Not ϕ INSERT H }
Proof
  ONCE_REWRITE_TAC [GSYM entails_constify] >>
  ‘∀P s. {FMC p | P p} = IMAGE FMC {x | P x}’
    by (simp[EXTENSION] >> metis_tac[IN_DEF]) >>
  dsimp[entails_def, hold_def, satisfiable_def, satisfies_def, PULL_EXISTS,
        holds_FMC_ARB, FMC_Not, language_NOT_INSERT] >>
  eq_tac >> rw[] >- (qexists_tac ‘M’ >> simp[]) >>
  qexists_tac ‘M’ >> simp[] >>
  ‘∃v:num -> α. valuation M v’ suffices_by metis_tac[] >>
  fs[valuation_def, EXTENSION] >> rename [‘d ∈ M.Dom’] >> qexists_tac ‘K d’ >>
  simp[]
QED

Theorem entails_mono:
  entails (:α) Γ₁ ϕ ∧ Γ₁ ⊆ Γ₂ ⇒ entails (:α) Γ₂ ϕ
Proof
  rw[entails_def, hold_def] >> last_x_assum irule >> simp[] >>
  ‘interpretation (language (ϕ INSERT Γ₁)) M’ suffices_by
    metis_tac[SUBSET_DEF] >>
  fs[language_def] >> irule interpretation_sublang >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  fs[SUBSET_DEF, functions_def] >> metis_tac[]
QED

Theorem satisfiable_antimono:
  satisfiable (:α) s₁ ∧ s₂ ⊆ s₁ ⇒ satisfiable (:α) s₂
Proof
  simp[satisfiable_def, SUBSET_DEF, satisfies_def] >> strip_tac >>
  ‘interpretation (language s₂) M’ suffices_by metis_tac[] >>
  fs[language_def] >> irule interpretation_sublang >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[functions_def, SUBSET_DEF, PULL_EXISTS] >> metis_tac[]
QED

Theorem tm_constify_11[simp]:
  ∀t1 t2. tm_constify ks t1 = tm_constify ks t2 ⇔ t1 = t2
Proof
  Induct >> Cases_on ‘t2’ >> simp[] >> rw[]
  >- metis_tac[]
  >- metis_tac[] >>
  rw[EQ_IMP_THM] >> fs[LIST_EQ_REWRITE, EL_MAP] >>
  rfs[EL_MAP] >> metis_tac[MEM_EL]
QED

Theorem fm_constify_11[simp]:
  ∀f1 f2 ks. fm_constify ks f1 = fm_constify ks f2 ⇔ f1 = f2
Proof
  Induct >> Cases_on ‘f2’ >> csimp[INJ_MAP_EQ_IFF, INJ_IFF]
QED

Theorem finite_entailment:
  INFINITE 𝕌(:α) ⇒
    (entails (:α) Γ ϕ ⇔ ∃Γ₀. FINITE Γ₀ ∧ Γ₀ ⊆ Γ ∧ entails (:α) Γ₀ ϕ)
Proof
  strip_tac >> reverse eq_tac >- metis_tac[entails_mono] >> CCONTR_TAC >>
  fs[] >>
  pop_assum (fn th =>
    ‘∀Γ₀. FINITE Γ₀ ∧ Γ₀ ⊆ Γ ⇒ ¬entails (:α) Γ₀ ϕ’ by metis_tac[th]) >>
  fs[not_entails] >>
  ‘ffinsat (:α) { FMC p | p ∈ (Not ϕ) INSERT Γ }’
    suffices_by (
      strip_tac >> drule_all COMPACTNESS_satisfiable >>
      metis_tac[not_entails]
    ) >>
  simp[ffinsat_def] >> rpt strip_tac >>
  rename [‘FINITE t’, ‘t ⊆ _ ’] >>
  ‘satisfiable (:α) (FMC (Not ϕ) INSERT t)’
     suffices_by metis_tac[SUBSET_OF_INSERT, satisfiable_antimono] >>
  ‘∃t0. FMC (Not ϕ) INSERT t = {FMC p | p = Not ϕ ∨ p ∈ t0} ∧ FINITE t0 ∧
        t0 ⊆ Γ’ suffices_by metis_tac[] >>
  qexists_tac ‘PREIMAGE FMC t DELETE Not ϕ’ >>
  dsimp[EXTENSION] >> rw[]
  >- (rw[EQ_IMP_THM] >> fs[SUBSET_DEF] >> first_x_assum drule >>
      rw[] >> metis_tac[])
  >- (irule FINITE_PREIMAGE >> simp[]) >>
  fs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[]
QED

val _ = export_theory()
