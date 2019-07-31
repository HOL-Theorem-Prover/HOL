open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory

val _ = new_theory "folLang";

Theorem MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG


Definition LIST_UNION_def[simp]:
  (LIST_UNION [] = ∅) ∧
  (LIST_UNION (h::t) = h ∪ LIST_UNION t)
End

Theorem IN_LIST_UNION[simp]:
  x ∈ LIST_UNION l ⇔ ∃s. MEM s l ∧ x ∈ s
Proof
  Induct_on ‘l’ >> simp[] >> metis_tac[]
QED

Theorem FINITE_LIST_UNION[simp]:
  FINITE (LIST_UNION sets) ⇔ ∀s. MEM s sets ⇒ FINITE s
Proof
  Induct_on ‘sets’ >> simp[] >> metis_tac[]
QED

val _ = Datatype‘
  term = V num | Fn num (term list)
’;

val term_size_def = DB.fetch "-" "term_size_def"
val _ = export_rewrites ["term_size_def"]

Theorem term_size_lemma[simp]:
  ∀x l a. MEM a l ⇒ term_size a < 1 + (x + term1_size l)
Proof
  rpt gen_tac >> Induct_on ‘l’ >> simp[] >> rpt strip_tac >> simp[] >>
  res_tac >> simp[]
QED

Theorem term_induct:
  ∀P. (∀v. P (V v)) ∧ (∀n ts. (∀t. MEM t ts ⇒ P t) ⇒ P (Fn n ts)) ⇒
      ∀t. P t
Proof
  rpt strip_tac >>
  qspecl_then [‘P’, ‘λts. ∀t. MEM t ts ⇒ P t’]
    (assume_tac o SIMP_RULE bool_ss [])
    (TypeBase.induction_of “:term”) >> rfs[] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM]
QED

val _ = TypeBase.update_induction term_induct

Definition tswap_def[simp]:
  (tswap x y (V v) = if v = x then V y else if v = y then V x else V v) ∧
  (tswap x y (Fn f ts) = Fn f (MAP (tswap x y) ts))
Termination
  WF_REL_TAC ‘measure (term_size o SND o SND)’ >> simp[]
End

Definition FVT_def[simp]:
  (FVT (V v) = {v}) ∧
  (FVT (Fn s ts) = LIST_UNION (MAP FVT ts))
Termination
  WF_REL_TAC ‘measure term_size’ >> simp[]
End

Theorem FVT_FINITE[simp]:
  ∀t. FINITE (FVT t)
Proof
  ho_match_mp_tac term_induct >> simp[MEM_MAP, PULL_EXISTS]
QED

Theorem tswap_inv[simp]:
  ∀t. tswap x y (tswap x y t) = t
Proof
  ho_match_mp_tac term_induct >> rw[] >> simp[MAP_MAP_o, Cong MAP_CONG']
QED

Theorem tswap_id[simp]:
  ∀t. tswap x x t = t
Proof
  ho_match_mp_tac term_induct >> rw[] >> simp[MAP_MAP_o, Cong MAP_CONG']
QED

Theorem tswap_supp_id[simp]:
  ∀t. x ∉ FVT t ∧ y ∉ FVT t ⇒ (tswap x y t = t)
Proof
  ho_match_mp_tac term_induct >> rw[] >> fs[MAP_MAP_o, MEM_MAP] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rw[] >> first_x_assum irule >>
  metis_tac[MEM_EL]
QED

Definition termsubst_def[simp]:
  (termsubst v (V x) = v x) ∧
  (termsubst v (Fn f l) = Fn f (MAP (termsubst v) l))
Termination
  WF_REL_TAC ‘measure (term_size o SND)’ >> simp[]
End

Theorem termsubst_termsubst:
  ∀t i j. termsubst j (termsubst i t) = termsubst (termsubst j o i) t
Proof
  ho_match_mp_tac term_induct >>
  simp[MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG']
QED

Theorem termsubst_triv[simp]:
  ∀t. termsubst V t = t
Proof
  ho_match_mp_tac term_induct >> simp[Cong MAP_CONG']
QED

Theorem termsubst_valuation:
  ∀t v1 v2. (∀x. x ∈ FVT t ⇒ (v1 x = v2 x)) ⇒ (termsubst v1 t = termsubst v2 t)
Proof
  ho_match_mp_tac term_induct >> simp[MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  irule MAP_CONG' >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[]
QED

Theorem termsubst_fvt:
  ∀t i. FVT (termsubst i t) = { x | ∃y. y ∈ FVT t ∧ x ∈ FVT (i y) }
Proof
  ho_match_mp_tac term_induct >>
  simp[MAP_MAP_o, combinTheory.o_ABS_R, MEM_MAP, PULL_EXISTS] >> rpt strip_tac>>
  simp[Once EXTENSION,MEM_MAP,PULL_EXISTS] >> csimp[] >> metis_tac[]
QED

Theorem freshsubst_tswap:
  ∀t. y ∉ FVT t ⇒ (termsubst V⦇ x ↦ V y ⦈ t = tswap x y t)
Proof
  ho_match_mp_tac term_induct >> simp[MEM_MAP,combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >- (COND_CASES_TAC >> fs[]) >>
  irule MAP_CONG' >> simp[] >> metis_tac[]
QED

val _ = Datatype‘
  form = False
       | Pred num (term list)
       | IMP form form
       | FALL num form
’;

Definition Not_def:
  Not f = IMP f False
End

Definition True_def:
  True = Not False
End

Definition Or_def:
  Or p q = IMP (IMP p q) q
End

Definition And_def:
  And p q = Not (Or (Not p) (Not q))
End

Definition Iff_def:
  Iff p q = And (IMP p q) (IMP q p)
End

Definition Exists_def:
  Exists x p = Not (FALL x (Not p))
End

Definition term_functions_def[simp]:
  (term_functions (V v) = ∅) ∧
  (term_functions (Fn f args) =
     (f, LENGTH args) INSERT LIST_UNION (MAP term_functions args))
Termination
  WF_REL_TAC ‘measure term_size’ >> simp[]
End

Definition form_functions_def[simp]:
  (form_functions False = ∅) ∧
  (form_functions (Pred n ts) = LIST_UNION (MAP term_functions ts)) ∧
  (form_functions (IMP f1 f2) = form_functions f1 ∪ form_functions f2) ∧
  (form_functions (FALL x f) = form_functions f)
End

Definition form_predicates[simp]:
  (form_predicates False = ∅) ∧
  (form_predicates (Pred n ts) = {(n,LENGTH ts)}) ∧
  (form_predicates (IMP f1 f2) = form_predicates f1 ∪ form_predicates f2) ∧
  (form_predicates (FALL x f) = form_predicates f)
End

Theorem form_functions_Exists[simp]:
  form_functions (Exists x p) = form_functions p
Proof
  simp[Exists_def, Not_def]
QED

Theorem form_predicates_Exists[simp]:
  form_predicates (Exists x p) = form_predicates p
Proof
  simp[Exists_def, Not_def]
QED

Definition functions_def:
  functions fms = BIGUNION{form_functions f | f ∈ fms}
End

Definition predicates_def:
  predicates fms = BIGUNION {form_predicates f | f ∈ fms}
End

Definition language_def:
  language fms = (functions fms, predicates fms)
End

Theorem functions_SING[simp]:
  functions {f} = form_functions f
Proof
  simp[functions_def, Once EXTENSION]
QED

Theorem language_SING:
  language {p} = (form_functions p, form_predicates p)
Proof
  simp[functions_def, language_def, predicates_def] >> simp[Once EXTENSION]
QED

Definition FV_def[simp]:
  (FV False = ∅) ∧
  (FV (Pred _ ts) = LIST_UNION (MAP FVT ts)) ∧
  (FV (IMP f1 f2) = FV f1 ∪ FV f2) ∧
  (FV (FALL x f) = FV f DELETE x)
End

Theorem FV_extras[simp]:
  (FV True = ∅) ∧
  (FV (Not p) = FV p) ∧
  (FV (And p q) = FV p ∪ FV q) ∧
  (FV (Or p q) = FV p ∪ FV q) ∧
  (FV (Iff p q) = FV p ∪ FV q) ∧
  (FV (Exists x p) = FV p DELETE x)
Proof
  simp[Exists_def, And_def, Or_def, Iff_def, True_def, Not_def] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem language_FALL[simp]:
  language {FALL x p} = language {p}
Proof
  simp[language_def, predicates_def, EXTENSION]
QED

Theorem language_Exists[simp]:
  language {Exists x p} = language {p}
Proof
  simp[language_def, predicates_def, EXTENSION, Exists_def, Not_def]
QED

Definition BV_def[simp]:
  (BV False = ∅) ∧
  (BV (Pred _ _) = ∅) ∧
  (BV (IMP f1 f2) = BV f1 ∪ BV f2) ∧
  (BV (FALL x f) = x INSERT BV f)
End

Theorem FV_FINITE[simp]:
  ∀f. FINITE (FV f)
Proof
  Induct >> simp[MEM_MAP,PULL_EXISTS]
QED

Theorem BV_FINITE[simp]:
  ∀f. FINITE (BV f)
Proof
  Induct >> simp[]
QED

Definition VARIANT_def :
  VARIANT s = MAX_SET s + 1
End

Theorem VARIANT_FINITE:
  ∀s. FINITE s ⇒ VARIANT s ∉ s
Proof
  simp[VARIANT_def] >> rpt strip_tac >> drule_all in_max_set >> simp[]
QED

Theorem VARIANT_THM[simp]:
  VARIANT (FV t) ∉ FV t
Proof
  simp[VARIANT_FINITE]
QED

Definition formsubst_def[simp]:
  (formsubst v False = False) ∧
  (formsubst v (Pred p l) = Pred p (MAP (termsubst v) l)) ∧
  (formsubst v (IMP f1 f2) = IMP (formsubst v f1) (formsubst v f2)) ∧
  (formsubst v (FALL u f) =
     let v' = v⦇ u ↦ V u ⦈ ;
         z  = if ∃y. y ∈ FV (FALL u f) ∧ u ∈ FVT (v' y) then
                VARIANT (FV (formsubst v' f))
              else u
     in
       FALL z (formsubst v⦇ u ↦ V z ⦈ f))
End

Theorem formsubst_triv[simp]:
  formsubst V p = p
Proof
  Induct_on ‘p’ >> simp[Cong MAP_CONG', combinTheory.APPLY_UPDATE_ID]
QED

Theorem formsubst_valuation:
  ∀v1 v2. (∀x. x ∈ FV p ⇒ (v1 x = v2 x)) ⇒ (formsubst v1 p = formsubst v2 p)
Proof
  Induct_on ‘p’ >> simp[MEM_MAP, PULL_EXISTS, Cong MAP_CONG']
  >- (rw[] >> irule MAP_CONG' >> simp[] >> metis_tac[termsubst_valuation]) >>
  csimp[combinTheory.UPDATE_APPLY] >> rpt gen_tac >> strip_tac >>
  reverse COND_CASES_TAC >> simp[]
  >- (first_x_assum irule >> simp[combinTheory.APPLY_UPDATE_THM]) >>
  rename [‘VARIANT (FV (formsubst v1⦇ k ↦ V k⦈ form))’] >>
  ‘formsubst v1⦇k ↦ V k⦈ form = formsubst v2⦇k ↦ V k⦈ form’
    by (first_x_assum irule >> simp[combinTheory.APPLY_UPDATE_THM]) >>
  simp[] >>
  first_x_assum irule >> simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem formsubst_FV :
  ∀i. FV (formsubst i p) = { x | ∃y. y ∈ FV p ∧ x ∈ FVT (i y) }
Proof
  Induct_on ‘p’ >>
  simp[MEM_MAP, PULL_EXISTS, MAP_MAP_o, Cong MAP_CONG', termsubst_fvt]
  >- (simp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[])
  >- (simp[Once EXTENSION] >> metis_tac[]) >>
  csimp[combinTheory.UPDATE_APPLY] >> rpt gen_tac >>
  reverse COND_CASES_TAC
  >- (simp[Once EXTENSION] >> fs[] >>
      simp[combinTheory.APPLY_UPDATE_THM] >> qx_gen_tac ‘u’ >> eq_tac >>
      simp[PULL_EXISTS] >> qx_gen_tac ‘v’ >- (rw[] >> metis_tac[]) >>
      metis_tac[]) >>
  simp[Once EXTENSION, EQ_IMP_THM, PULL_EXISTS, FORALL_AND_THM] >>
  qmatch_goalsub_abbrev_tac ‘i ⦇ n ↦ V var⦈’ >> rw[]
  >- (rename [‘x ∈ FVT (i ⦇ n ↦ V var ⦈ y)’] >>
      ‘y ≠ n’ by (strip_tac >> fs[combinTheory.UPDATE_APPLY]) >>
      fs[combinTheory.UPDATE_APPLY] >> metis_tac[]) >>
  asm_simp_tac (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.COND_elim_ss)
               [combinTheory.APPLY_UPDATE_THM] >>
  simp[GSYM PULL_EXISTS] >> conj_tac >- metis_tac[] >>
  simp[Abbr‘var’] >>
  last_assum (fn th => REWRITE_TAC [GSYM th]) >>
  qmatch_abbrev_tac‘x <> VARIANT (FV f)’ >>
  ‘x ∈ FV f’ suffices_by metis_tac[VARIANT_THM] >>
  simp[Abbr‘f’] >> metis_tac[combinTheory.APPLY_UPDATE_THM]
QED

Theorem VARIANT_NOTIN_SUBSET:
  FINITE s ∧ t ⊆ s ⇒ VARIANT s ∉ t
Proof
  simp[VARIANT_def] >> strip_tac >> DEEP_INTRO_TAC MAX_SET_ELIM >> simp[] >>
  rw[] >> fs[] >> metis_tac [DECIDE “~(x + 1 ≤ x)”, SUBSET_DEF]
QED

Theorem formsubst_rename:
  FV (formsubst V⦇ x ↦ V y⦈ p) DELETE y = (FV p DELETE x) DELETE y
Proof
  simp_tac (srw_ss() ++ boolSimps.COND_elim_ss ++ boolSimps.CONJ_ss)
    [formsubst_FV, EXTENSION, combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem term_functions_termsubst:
  ∀t i. term_functions (termsubst i t) =
        term_functions t ∪ { x | ∃y. y ∈ FVT t ∧ x ∈ term_functions (i y) }
Proof
  ho_match_mp_tac term_induct >>
  simp[MAP_MAP_o, combinTheory.o_ABS_R, MEM_MAP, PULL_EXISTS, Cong MAP_CONG'] >>
  rpt strip_tac >> simp[Once EXTENSION] >> simp[MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem form_functions_formsubst:
  ∀i. form_functions (formsubst i p) =
      form_functions p ∪ { x | ∃y. y ∈ FV p ∧ x ∈ term_functions (i y) }
Proof
  Induct_on ‘p’ >>
  simp[MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG',
       term_functions_termsubst, MEM_MAP, PULL_EXISTS]
  >- (simp[Once EXTENSION,MEM_MAP, PULL_EXISTS] >> metis_tac[])
  >- (simp[Once EXTENSION] >> metis_tac[])
  >- (csimp[combinTheory.APPLY_UPDATE_THM] >>
      simp_tac (srw_ss() ++ boolSimps.COND_elim_ss ++ boolSimps.CONJ_ss) [] >>
      simp[Once EXTENSION] >> metis_tac[])
QED


Theorem form_functions_formsubst1[simp]:
  x ∈ FV p ⇒
  (form_functions (formsubst V⦇ x ↦ t ⦈ p) =
   form_functions p ∪ term_functions t)
Proof
  simp_tac(srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.COND_elim_ss)
    [combinTheory.APPLY_UPDATE_THM,form_functions_formsubst,
     term_functions_termsubst]
QED

Theorem form_predicates_formsubst[simp]:
  ∀i. form_predicates (formsubst i p) = form_predicates p
Proof   Induct_on ‘p’ >> simp[]
QED

Theorem formsubst_14b[simp]:
  x ∉ FV p ⇒ (formsubst V⦇ x ↦ t ⦈ p = p)
Proof
  strip_tac >>
  ‘formsubst V⦇x ↦ t⦈ p = formsubst V p’ suffices_by simp[] >>
  irule formsubst_valuation >>
  asm_simp_tac(srw_ss() ++ boolSimps.COND_elim_ss ++ boolSimps.CONJ_ss)
    [combinTheory.APPLY_UPDATE_THM]
QED

Theorem formsubst_language_rename:
  language {formsubst V⦇ x ↦ V y ⦈ p} = language {p}
Proof
  simp[language_SING] >> Cases_on ‘x ∈ FV p’ >> simp[]
QED

(* TODO: show formulas are countable set *)

val _ = export_theory();
