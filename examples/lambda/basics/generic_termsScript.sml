(* ========================================================================== *)
(* FILE    : generic_termsScript.sml                                          *)
(* TITLE   : Theory of generic terms with binders                             *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open BasicProvers boolSimps pred_setTheory listTheory quotientLib;
open relationTheory;

open binderLib basic_swapTheory nomsetTheory;

val _ = new_theory "generic_terms";

val _ = computeLib.auto_import_definitions := false;

Datatype:
  pregterm = lam string (string list) 'b (pregterm list) (pregterm list)
End

Definition fv_def:
  fv (lam v fvs bv bndts unbndts) =
   (fvl bndts DELETE v) ∪ fvl unbndts ∪ set fvs ∧
  fvl [] = ∅ ∧
  fvl (h::ts) = fv h ∪ fvl ts
End
val _ = augment_srw_ss [rewrites [fv_def]]

val oldind = TypeBase.induction_of ``:α pregterm``

Theorem pind[local]:
  ∀P.
      (∀v bv fvs bndts unbndts.
         EVERY P bndts ∧ EVERY P unbndts ⇒ P (lam v fvs bv bndts unbndts))
    ⇒
      ∀t. P t
Proof
  gen_tac >> strip_tac >>
  Q_TAC suff_tac `(∀t. P t) ∧ (∀ts. EVERY P ts)` >- metis_tac [] >>
  ho_match_mp_tac oldind >> srw_tac [][]
QED

Theorem fvl_thm:
  fvl ts = BIGUNION (IMAGE fv (set ts))
Proof
  Induct_on ‘ts’ >> simp[]
QED

Theorem finite_fv:
  ∀t. FINITE (fv t)
Proof
  Induct_on ‘t’ using pind >> gvs[fvl_thm, PULL_EXISTS, EVERY_MEM]
QED
val _ = augment_srw_ss [rewrites [finite_fv]]

Definition raw_ptpm_def:
  raw_ptpm p (lam v fvs bv bndts unbndts) =
   lam (lswapstr p v) (listpm string_pmact p fvs) bv
       (raw_ptpml p bndts) (raw_ptpml p unbndts) ∧
  (raw_ptpml p [] = []) ∧
  (raw_ptpml p (h::t) = raw_ptpm p h :: raw_ptpml p t)
End

Overload pt_pmact = “mk_pmact raw_ptpm”
Overload ptpm = “pmact pt_pmact”
Overload ptl_pmact = “mk_pmact raw_ptpml”
Overload ptpml = “pmact ptl_pmact”

Theorem raw_ptpm_nil[local]:
  (∀t:α pregterm. raw_ptpm [] t = t) ∧
  (∀l:α pregterm list. raw_ptpml [] l = l)
Proof
  ho_match_mp_tac oldind >> srw_tac [][raw_ptpm_def]
QED

Theorem raw_ptpm_compose[local]:
  (∀t:α pregterm. raw_ptpm p1 (raw_ptpm p2 t) = raw_ptpm (p1 ++ p2) t) ∧
  (∀l:α pregterm list.
     raw_ptpml p1 (raw_ptpml p2 l) = raw_ptpml (p1 ++ p2) l)
Proof
  ho_match_mp_tac oldind >> srw_tac [][raw_ptpm_def, pmact_decompose]
QED

Theorem raw_ptpm_permeq[local]:
  (∀x. lswapstr p1 x = lswapstr p2 x) ⇒
  (∀t:α pregterm. raw_ptpm p1 t = raw_ptpm p2 t) ∧
  (∀l:α pregterm list. raw_ptpml p1 l = raw_ptpml p2 l)
Proof
  strip_tac >> ho_match_mp_tac oldind >> srw_tac [][raw_ptpm_def] >>
  AP_THM_TAC >> irule listpm_permeq >>
  gvs[permeq_def, stringpm_raw, FUN_EQ_THM]
QED

Theorem ptpm_raw[local]:
  (ptpm = raw_ptpm) ∧ (ptpml = raw_ptpml)
Proof
  conj_tac >> (
  srw_tac [][GSYM pmact_bijections] >>
  srw_tac [][is_pmact_def] >|[
    srw_tac [][raw_ptpm_nil],
    srw_tac [][raw_ptpm_compose],
    fsrw_tac [][raw_ptpm_permeq, permeq_thm, FUN_EQ_THM]
  ])
QED
Theorem ptpm_raw[local,allow_rebind] = INST_TYPE[beta|->alpha] ptpm_raw

Theorem ptpml_listpm:
  ∀l. ptpml p l = listpm pt_pmact p l
Proof
  Induct >> fsrw_tac[][ptpm_raw] >>
  srw_tac [][raw_ptpm_def]
QED

(* |- !p v bv bndts unbndts.
        ptpm p (lam v bv bndts unbndts) =
        lam (lswapstr p v) bv (listpm pt_pmact p bndts)
          (listpm pt_pmact p unbndts)
 *)
Theorem ptpm_thm[simp] =
  raw_ptpm_def |> CONJUNCTS |> hd
               |> SUBS (map GSYM (CONJUNCTS ptpm_raw))
               |> REWRITE_RULE [ptpml_listpm]

Theorem ptpm_fv:
  (∀t:α pregterm. fv (ptpm p t) = ssetpm p (fv t)) ∧
  (∀l:α pregterm list. fvl (ptpml p l) = ssetpm p (fvl l))
Proof
  ho_match_mp_tac oldind >>
  srw_tac[][stringpm_raw, ptpml_listpm, pmact_INSERT, pmact_DELETE, pmact_UNION,
            set_listpm]
QED
val _ = augment_srw_ss [rewrites [ptpm_fv]]

Definition allatoms_def:
  (allatoms (lam v fvs bv bndts unbndts) =
     v INSERT allatomsl bndts ∪ allatomsl unbndts ∪ set fvs) ∧
  (allatomsl [] = ∅) ∧
  (allatomsl (t::ts) = allatoms t ∪ allatomsl ts)
End

Theorem allatoms_finite[simp] :
    (∀t:α pregterm. FINITE (allatoms t)) ∧
    (∀l:α pregterm list. FINITE (allatomsl l))
Proof
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def]
QED

Theorem allatoms_supports:
  (∀t:α pregterm. support pt_pmact t (allatoms t)) ∧
  (∀l:α pregterm list. support (list_pmact pt_pmact) l (allatomsl l))
Proof
  simp_tac (srw_ss())[support_def] >>
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def] >>
  rename [‘listpm string_pmact [(x,y)] l = l’] >>
  map_every (C qpat_x_assum mp_tac) [‘¬MEM x l’, ‘¬MEM y l’] >>
  Induct_on ‘l’ >> simp[]
QED

Theorem allatoms_fresh:
  x ∉ allatoms t ∧ y ∉ allatoms t ==> ptpm [(x,y)] t = t
Proof
  METIS_TAC [allatoms_supports, support_def]
QED

Theorem lswapstrl_apart:
  ¬MEM a l ∧ MEM b l ⇒ listpm string_pmact [(a,b)] l ≠ l
Proof
  Induct_on ‘l’ >> dsimp[]
QED

Theorem lswapstrl_fresh:
  ¬MEM a l ∧ ¬MEM b l ⇒ listpm string_pmact [(a,b)] l = l
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem allatoms_apart:
  (∀t:α pregterm a b.
     a ∉ allatoms t /\ b ∈ allatoms t ⇒ ptpm [(a,b)] t ≠ t) ∧
  (∀l:α pregterm list a b.
     a ∉ allatomsl l ∧ b ∈ allatomsl l ⇒ listpm pt_pmact [(a,b)] l ≠ l)
Proof
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def] >>
  metis_tac[swapstr_def, lswapstrl_apart]
QED

Theorem allatoms_supp:
  supp pt_pmact t = allatoms t
Proof
  MATCH_MP_TAC supp_unique >>
  SRW_TAC [][allatoms_supports, SUBSET_DEF] >>
  fs[support_def] >>
  SPOSE_NOT_THEN ASSUME_TAC >>
  rename [‘x ∈ allatoms t’, ‘x ∉ A’] >>
  ‘?y. y NOTIN allatoms t ∧ y NOTIN A’
     by (Q.SPEC_THEN ‘allatoms t UNION A’ MP_TAC NEW_def THEN
         SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC [allatoms_apart]
QED

Theorem allatoms_perm:
  (∀t:α pregterm. allatoms (ptpm p t) = ssetpm p (allatoms t)) ∧
  (∀l:α pregterm list.
     allatomsl (listpm pt_pmact p l) = ssetpm p (allatomsl l))
Proof
  ho_match_mp_tac oldind >>
  srw_tac [][allatoms_def, pmact_INSERT, pmact_UNION, set_listpm]
QED

Inductive aeq:
[~lam:]
  (!u v fvs bv z bndts1 bndts2 us1 us2.
      aeql us1 us2 ∧
      aeql (ptpml [(u,z)] bndts1) (ptpml [(v,z)] bndts2) ∧
      z ∉ allatomsl bndts1 ∧ z ∉ allatomsl bndts2 ∧ z ≠ u ∧ z ≠ v ⇒
      aeq (lam u fvs bv bndts1 us1) (lam v fvs bv bndts2 us2))
[~nil:]
  aeql [] []
[~cons:]
  (∀h1 h2 t1 t2. aeq h1 h2 ∧ aeql t1 t2 ⇒ aeql (h1::t1) (h2::t2))
End

Theorem aeq_ptpm_lemma:
  (!t:α pregterm u. aeq t u ==> !p. aeq (ptpm p t) (ptpm p u)) ∧
  (∀ts:α pregterm list us.
      aeql ts us ⇒ ∀π. aeql (listpm pt_pmact π ts) (listpm pt_pmact π us))
Proof
  ho_match_mp_tac aeq_ind >> srw_tac [][aeq_rules, ptpml_listpm] >>
  match_mp_tac aeq_lam >>
  Q.EXISTS_TAC `lswapstr p z` THEN
  srw_tac [][allatoms_perm, pmact_IN] >>
  srw_tac [][ptpml_listpm, pmact_sing_to_back]
QED

Theorem aeq_ptpm_eqn:
  aeq (ptpm p t) u = aeq t (ptpm (REVERSE p) u)
Proof METIS_TAC [aeq_ptpm_lemma, pmact_inverse]
QED

Theorem aeql_ptpm_eqn:
  aeql (ptpml p l1) l2 = aeql l1 (ptpml p⁻¹ l2)
Proof METIS_TAC [aeq_ptpm_lemma, ptpml_listpm, pmact_inverse]
QED

Theorem IN_fvl[local]:
  x ∈ fvl tl ⇔ ∃e. MEM e tl ∧ x ∈ fv e
Proof
  Induct_on `tl` >> srw_tac [DNF_ss][AC DISJ_ASSOC DISJ_COMM]
QED

Theorem IN_allatomsl[local]:
  x ∈ allatomsl tl ⇔ ∃t. MEM t tl ∧ x ∈ allatoms t
Proof
  Induct_on `tl` >> srw_tac [DNF_ss][allatoms_def]
QED

Theorem fv_SUBSET_allatoms:
  (∀t:α pregterm. fv t SUBSET allatoms t) ∧
  (∀l:α pregterm list. fvl l ⊆ allatomsl l)
Proof
  SIMP_TAC (srw_ss()) [SUBSET_DEF] >> ho_match_mp_tac oldind>>
  srw_tac [][allatoms_def] >> metis_tac []
QED

Theorem aeq_fv:
  (!t:α pregterm u. aeq t u ==> (fv t = fv u)) ∧
  (∀ts:α pregterm list us. aeql ts us ⇒ (fvl ts = fvl us))
Proof
  ho_match_mp_tac aeq_ind >>
  srw_tac [][EXTENSION, ptpm_fv, pmact_IN, ptpml_listpm] THEN
  Cases_on `x ∈ fvl us` >> srw_tac [][] >>
  Cases_on `x = u` >> srw_tac [][] THENL [
    Cases_on `u = v` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `swapstr v z u` (MP_TAC o SYM)) THEN
    SRW_TAC [][] THEN SRW_TAC [][swapstr_def] THEN
    METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
    Cases_on `x = v` THEN SRW_TAC [][] THENL [
      FIRST_X_ASSUM (Q.SPEC_THEN `swapstr u z v` MP_TAC) THEN
      SRW_TAC [][] THEN SRW_TAC [][swapstr_def] THEN
      METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
      Cases_on `z = x` THEN SRW_TAC [][] THENL [
        METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
        FIRST_X_ASSUM (Q.SPEC_THEN `x` MP_TAC) THEN
        SRW_TAC [][swapstr_def]
      ]
    ]
  ]
QED

Theorem aeq_refl[simp] :
  (∀t:α pregterm. aeq t t) ∧ (∀l:α pregterm list. aeql l l)
Proof
  ho_match_mp_tac oldind >> asm_simp_tac (srw_ss())[aeq_rules] >>
  REPEAT gen_tac >> strip_tac >>
  qx_genl_tac [‘b’, ‘bvs’, ‘v’] >>
  MATCH_MP_TAC aeq_lam >>
  SRW_TAC [][aeql_ptpm_eqn, ptpml_listpm] THEN
  Q.SPEC_THEN `v INSERT allatomsl l` MP_TAC NEW_def THEN SRW_TAC [][] THEN
  METIS_TAC []
QED

Theorem aeq_sym:
  (∀t:α pregterm u. aeq t u ==> aeq u t) ∧
  (∀l1:α pregterm list l2. aeql l1 l2 ==> aeql l2 l1)
Proof
  ho_match_mp_tac aeq_ind >> srw_tac [][aeq_rules] >>
  metis_tac [aeq_lam]
QED

Theorem aeq_lam_inversion:
  aeq (lam v fvs bv bndts unbndts) N ⇔
      ∃z v' bndts' unbndts'.
        (N = lam v' fvs bv bndts' unbndts') ∧ z ≠ v' ∧ z ≠ v ∧
        z ∉ allatomsl bndts ∧ z ∉ allatomsl bndts' ∧
        aeql (ptpml [(v,z)] bndts) (ptpml [(v',z)] bndts') ∧
        aeql unbndts unbndts'
Proof
  srw_tac [][Once aeq_cases, SimpLHS] >> metis_tac []
QED

Theorem aeq_ptm_11:
    (aeq (lam v fvs1 bv1 bndts1 unbndts1) (lam v fvs2 bv2 bndts2 unbndts2) ⇔
      bv1 = bv2 ∧ fvs1 = fvs2 ∧ aeql bndts1 bndts2 ∧ aeql unbndts1 unbndts2)
Proof
  SRW_TAC [][aeq_lam_inversion, aeq_ptpm_eqn, EQ_IMP_THM]
  THENL [
    full_simp_tac (srw_ss() ++ ETA_ss)
      [aeql_ptpm_eqn, pmact_nil],
    srw_tac [][],
    Q_TAC (NEW_TAC "z") `v INSERT allatomsl bndts1 ∪ allatomsl bndts2` THEN
    Q.EXISTS_TAC `z` >>
    srw_tac [ETA_ss][aeql_ptpm_eqn]
  ]
QED

val ptpml_fresh =
  allatoms_supports |> CONJUNCT2 |>
  SIMP_RULE (srw_ss()) [support_def, GSYM ptpml_listpm]

Theorem ptpml_sing_to_back'[local]:
  ptpml p (ptpml [(u,v)] tl) =
       ptpml [(lswapstr p u, lswapstr p v)] (ptpml p tl)
Proof simp[pmact_sing_to_back]
QED

(* proof follows that on p169 of Andy Pitts, Information and Computation 186
   article: Nominal logic, a first order theory of names and binding *)
Theorem aeq_trans:
  (∀t:α pregterm u. aeq t u ⇒ ∀v. aeq u v ==> aeq t v) ∧
  (∀l1:α pregterm list l2. aeql l1 l2 ⇒ ∀l3. aeql l2 l3 ⇒ aeql l1 l3)
Proof
  ho_match_mp_tac aeq_ind >> REPEAT conj_tac >> simp[] >~
  [‘aeq (lam _ _ _ _ _) _ ⇒ aeq (lam _ _ _ _ _ ) _’]
  >- (‘∀u v fvs bv z bt1 bt2 ut1 (ut2:α pregterm list).
         (∀l3. aeql (ptpml [(v,z)] bt2) l3 ⇒ aeql (ptpml [(u,z)] bt1) l3) ∧
         (∀ut3. aeql ut2 ut3 ⇒ aeql ut1 ut3) ∧
         z ∉ allatomsl bt1 ∧ z ∉ allatomsl bt2 ∧ z ≠ u ∧ z ≠ v ⇒
         ∀t3. aeq (lam v fvs bv bt2 ut2) t3 ⇒ aeq (lam u fvs bv bt1 ut1) t3’
        suffices_by metis_tac [] >>
      rpt gen_tac >> strip_tac >> gen_tac >>
      simp_tac (srw_ss()) [SimpL “$==>”, aeq_lam_inversion] >>
      disch_then $ qx_choosel_then[‘z2’, ‘w’, ‘bt3’, ‘ut3’] strip_assume_tac >>
      Q_TAC (NEW_TAC "d")
            ‘{z;z2;u;v;w} ∪ allatomsl bt1 ∪ allatomsl bt2 ∪ allatomsl bt3’ >>
      ‘∀bt3.
           aeql (ptpml [(z,d)] (ptpml [(v,z)] bt2)) (ptpml [(z,d)] bt3) ==>
        aeql (ptpml [(z,d)] (ptpml [(u,z)] bt1)) (ptpml [(z,d)] bt3)’
         by FULL_SIMP_TAC (srw_ss()) [aeql_ptpm_eqn] THEN
        POP_ASSUM
          (Q.SPEC_THEN ‘ptpml [(z,d)] bt3’
            (ASSUME_TAC o Q.GEN ‘bt3’ o
             SIMP_RULE (srw_ss() ++ ETA_ss)
                       [pmact_sing_inv, pmact_nil])) THEN
        POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ptpml_sing_to_back']) THEN
        SRW_TAC [][swapstr_def, ptpml_fresh] THEN
        ‘aeql (ptpml [(z2,d)] (ptpml [(v,z2)] bt2))
         (ptpml [(z2,d)] (ptpml [(w,z2)] bt3))’
          by (srw_tac [ETA_ss]
                      [Once aeql_ptpm_eqn, pmact_nil]) >>
        POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ptpml_sing_to_back']) THEN
        SRW_TAC [][swapstr_def, ptpml_fresh] THEN
        ‘aeql (ptpml [(u,d)] bt1) (ptpml [(w,d)] bt3)’ by METIS_TAC [] THEN
        METIS_TAC [aeq_lam]) >~
  [‘aeql  (_ :: _) _ ⇒ aeql (_ :: _) _’] >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  srw_tac [][Once aeq_cases, SimpL “$==>”] >>
  metis_tac [aeq_rules]
QED

Theorem aeq_equiv:
  !t1 t2. aeq t1 t2 = (aeq t1 = aeq t2)
Proof
  srw_tac [][FUN_EQ_THM] >> METIS_TAC [aeq_trans, aeq_sym, aeq_refl]
QED

val alt_aeq_lam = store_thm(
  "alt_aeq_lam",
  ``(∀z. z ∉ allatomsl t1 ∧ z ∉ allatomsl t2 ∧ z ≠ u ∧ z ≠ v ⇒
         aeql (ptpml [(u,z)] t1) (ptpml [(v,z)] t2)) ∧
    aeql u1 u2 ⇒
    aeq (lam u fvs bv t1 u1) (lam v fvs bv t2 u2)``,
  strip_tac >> MATCH_MP_TAC aeq_lam >>
  Q_TAC (NEW_TAC "z")
     `allatomsl t1 ∪ allatomsl t2 ∪ {u;v}` >>
  METIS_TAC []);

Theorem fresh_swap:
  (∀t:α pregterm x y. x ∉ fv t ∧ y ∉ fv t ⇒ aeq t (ptpm [(x, y)] t)) ∧
  (∀l:α pregterm list x y.
     x ∉ fvl l ∧ y ∉ fvl l ⇒ aeql l (ptpml [(x,y)] l))
Proof
  ho_match_mp_tac oldind >>
  asm_simp_tac (srw_ss()) [aeq_rules,ptpml_listpm] >>
  map_every qx_gen_tac [`bt`, `ut`] >> strip_tac >>
  qx_genl_tac [`b`, ‘fvs’, `s`,`x`,`y`] >>
  strip_tac >> srw_tac [][lswapstrl_fresh] >>
  match_mp_tac alt_aeq_lam >> rpt strip_tac >>
  fsrw_tac [][pmact_id, pmact_nil, GSYM ptpml_listpm] >>
  `z ∉ fvl bt` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] >| [
    Cases_on `s = x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
      SRW_TAC [][swapstr_def, aeql_ptpm_eqn, pmact_sing_inv,
                 pmact_id, pmact_nil],
      ALL_TAC
    ] THEN Cases_on `s = y` THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
      SRW_TAC [][swapstr_def, pmact_flip_args, aeql_ptpm_eqn,
                 pmact_sing_inv],
      SRW_TAC [][swapstr_def, aeql_ptpm_eqn, pmact_sing_inv]
    ],
    Cases_on `s = x` THEN1 SRW_TAC [][pmact_id, pmact_nil] THEN
    ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
    SRW_TAC [][swapstr_def, pmact_flip_args, aeql_ptpm_eqn, pmact_sing_inv],
    Cases_on `s = y` THEN1 SRW_TAC [][pmact_id, pmact_nil] THEN
    ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
    SRW_TAC [][swapstr_def, aeql_ptpm_eqn, pmact_sing_inv]
  ]
QED

Theorem lam_aeq_thm:
    aeq (lam v1 fvs1 bv1 t1 u1) (lam v2 fvs2 bv2 t2 u2) ⇔
       (v1 = v2) ∧ (bv1 = bv2) ∧ fvs1 = fvs2 ∧ aeql t1 t2 ∧ aeql u1 u2 ∨
       v1 ≠ v2 ∧ (bv1 = bv2) ∧ fvs1 = fvs2 ∧ v1 ∉ fvl t2 ∧
       aeql t1 (ptpml [(v1,v2)] t2) ∧ aeql u1 u2
Proof
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, DISJ_IMP_THM] THEN REPEAT CONJ_TAC THENL [
    srw_tac [][aeq_lam_inversion] >>
    `z ∉ fvl t1 ∧ z ∉ fvl t2`
       by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] >>
    Cases_on `v1 = v2` >- fsrw_tac [][aeql_ptpm_eqn, pmact_sing_inv] THEN
    `v1 ∉ fvl t2`
        by (strip_tac >>
            `v1 ∈ fvl (ptpml [(v2,z)] t2)`
               by SRW_TAC [][ptpm_fv, pmact_IN] THEN
            `v1 ∈ fvl (ptpml [(v1,z)] t1)` by metis_tac [aeq_fv] THEN
            fsrw_tac [][ptpm_fv, pmact_IN, ptpml_listpm]) >>
    fsrw_tac [][aeql_ptpm_eqn] >>
    Q.PAT_X_ASSUM `aeql X (ptpml PPI Y)` MP_TAC THEN
    SRW_TAC [][swapstr_def, Once ptpml_sing_to_back'] THEN
    MATCH_MP_TAC (MP_CANON (CONJUNCT2 aeq_trans)) THEN
    Q.EXISTS_TAC `ptpml [(v1,v2)] (ptpml [(v1,z)] t2)`  THEN
    FULL_SIMP_TAC (srw_ss()) [pmact_flip_args, aeql_ptpm_eqn, fresh_swap,
                              pmact_sing_inv],

    srw_tac [][] >> match_mp_tac alt_aeq_lam >>
    srw_tac [][aeql_ptpm_eqn, pmact_sing_inv],

    srw_tac [][] >> match_mp_tac alt_aeq_lam >>
    srw_tac [][aeql_ptpm_eqn] >>
    `z ∉ fvl t2` by metis_tac [SUBSET_DEF, fv_SUBSET_allatoms] >>
    SRW_TAC [][swapstr_def, pmact_flip_args, Once ptpml_sing_to_back'] >>
    match_mp_tac (MP_CANON (CONJUNCT2 aeq_trans)) >>
    qexists_tac `ptpml [(v1,v2)] t2` >>
    srw_tac [][aeql_ptpm_eqn, fresh_swap, pmact_sing_inv, pmact_flip_args]
  ]
QED

val aeql_LIST_REL = prove(
  ``aeql l1 l2 ⇔ LIST_REL aeq l1 l2``,
  map_every Q.ID_SPEC_TAC [`l2`, `l1`] >> Induct >>
  srw_tac [][Once aeq_cases] >> Cases_on `l2` >>
  srw_tac [][]);

val lam_respects_aeq = store_thm(
  "lam_respects_aeq",
  ``!v fvs bv t1 t2 u1 u2.
      aeql t1 t2 ∧ aeql u1 u2 ==> aeq (lam v fvs bv t1 u1) (lam v fvs bv t2 u2)``,
  srw_tac [][] >> match_mp_tac aeq_lam >>
  srw_tac [][aeql_ptpm_eqn, pmact_sing_inv] >>
  Q_TAC (NEW_TAC "z") `v INSERT allatomsl t1 ∪ allatomsl t2` >> metis_tac []);

val rmaeql = REWRITE_RULE [aeql_LIST_REL]

(* ----------------------------------------------------------------------
    perform quotient!
   ---------------------------------------------------------------------- *)

fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = NONE, fname = s, func = t};

val ptpm_fv' =
    ptpm_fv |> CONJUNCT1 |> REWRITE_RULE [EXTENSION]
            |> CONV_RULE
                 (STRIP_QUANT_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [pmact_IN])))
            |> SIMP_RULE std_ss [ptpm_raw]

val fvl_MAP = prove(
  ``fvl l = BIGUNION (set (MAP fv l))``,
  Induct_on `l` >> srw_tac [][]);
val rmfvl = REWRITE_RULE [fvl_MAP]

val ptpml_MAP = prove(
  ``ptpml p l = MAP (raw_ptpm p) l``,
  Induct_on `l` >> fsrw_tac [][ptpm_raw,raw_ptpm_def]);
val rmptpml = REWRITE_RULE [GSYM ptpml_listpm,ptpml_MAP,ptpm_raw]

fun front n l = List.take (l, n)
fun drop n l = List.drop(l,n)

Theorem fvl_eqrespects[local]:
  ∀ts1 ts2:α pregterm list. (ts1 = ts2) ==> (fvl ts1 = fvl ts2)
Proof srw_tac [][]
QED

val pregterm_size_thm = TypeBase.size_of “:'a pregterm”
Definition psize_def:
  (psize (lam s fvs bv ts us) =
   SUM (MAP psize ts) + SUM (MAP psize us) + LENGTH fvs + 1)
End

val psize_thm = SIMP_RULE (srw_ss()++ETA_ss) [] psize_def

Theorem psize_ptpm0[local]:
  (∀p:α pregterm pi. psize (ptpm pi p) = psize p) /\
  (∀pl:α pregterm list pi. MAP psize (ptpml pi pl) = MAP psize pl)
Proof
  ho_match_mp_tac oldind >>
  srw_tac [][psize_thm, ptpml_listpm]
QED

val psize_raw_ptpm = psize_ptpm0 |> CONJUNCT1 |> REWRITE_RULE [ptpm_raw]

Theorem psize_respects[local]:
  ∀t1 t2. aeq t1 t2 ⇒ (psize t1 = psize t2)
Proof
  ‘(∀(t1:'a pregterm) t2. aeq t1 t2 ⇒ (psize t1 = psize t2)) ∧
   (∀(l1:'a pregterm list) l2.
      aeql l1 l2 ⇒ (SUM (MAP psize l1) = SUM (MAP psize l2)))’
    suffices_by metis_tac [] >>
  ho_match_mp_tac aeq_ind >>
  srw_tac [][psize_thm] >>
  fsrw_tac [][psize_ptpm0]
QED

val [GFV_thm0, gfvl_thm, GFV_raw_gtpm, simple_induction0,
     raw_gtpm_thm, is_pmact_raw_gtpm,
     gterm_11,
     GLAM_eq_thm0, FRESH_swap0,
     FINITE_GFV, gtmsize_thm, gtmsize_raw_gtpm] =
    quotient.define_quotient_types_full
    {
     types = [{name = "gterm", equiv = aeq_equiv}],
     defs = map mk_def
       [("GLAM", ``lam:string -> string list -> α -> α pregterm list ->
                       α pregterm list -> α pregterm``),
        ("GFV", ``fv : α pregterm -> string set``),
        ("gfvl", ``fvl : α pregterm list -> string set``),
        ("raw_gtpm", ``raw_ptpm : pm -> α pregterm -> α pregterm``),
        ("gtmsize", ``psize:α pregterm ->num``)],
     tyop_equivs = [],
     tyop_quotients = [],
     tyop_simps = [],
     respects = [rmaeql lam_respects_aeq,
                 CONJUNCT1 aeq_fv,
                 rmaeql (CONJUNCT2 aeq_fv),
                 aeq_ptpm_lemma
                     |> CONJUNCT1
                     |> SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, ptpm_raw],
                 (*aeq_ptpm_lemma
                     |> CONJUNCT2
                     |> SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, GSYM ptpml_listpm]
                     |> rmptpml, *)
                 psize_respects
                 ],
     poly_preserves = [],
     poly_respects = [],
     old_thms = [fv_def |> CONJUNCTS |> hd,
                 fv_def |> CONJUNCTS |> tl |> LIST_CONJ,
                 ptpm_fv', pind,
                 ptpm_thm |> rmptpml,
                 is_pmact_pmact |> Q.ISPEC ‘pt_pmact’
                                |> REWRITE_RULE [ptpm_raw,is_pmact_def],
                 rmaeql aeq_ptm_11,
                 rmptpml (rmaeql lam_aeq_thm),
                 CONJUNCT1 fresh_swap |> REWRITE_RULE [ptpm_raw],
                 finite_fv,
                 psize_thm, psize_raw_ptpm]}

Theorem simple_induction =
  REWRITE_RULE [EVERY_MEM] simple_induction0

Overload gt_pmact = ``mk_pmact raw_gtpm``
Overload gtpm = ``pmact gt_pmact``

Theorem gtpm_raw:
  gtpm = raw_gtpm
Proof
  srw_tac [][GSYM pmact_bijections,is_pmact_def,is_pmact_raw_gtpm]
QED

Theorem gtpm_thm = raw_gtpm_thm |> SUBS [GSYM gtpm_raw]

val GFV_support = prove(
  ``support gt_pmact t (GFV t)``,
  srw_tac [][support_def, GSYM FRESH_swap0, gtpm_raw])

val MAP_EQ1 = prove(
  ``(MAP f l = l) ⇔ ∀x. MEM x l ⇒ (f x = x)``,
  Induct_on `l` >> srw_tac [][DISJ_IMP_THM, FORALL_AND_THM]);

val IN_gfvl = prove(
  ``x ∈ gfvl ts ⇔ ∃t. MEM t ts ∧ x ∈ GFV t``,
  Induct_on `ts` >> srw_tac [][gfvl_thm] >> metis_tac []);

val GFV_apart = prove(
  ``∀t x y. x ∈ GFV t ∧ y ∉ GFV t ⇒ gtpm [(x,y)] t ≠ t``,
  ho_match_mp_tac simple_induction >>
  srw_tac [][GFV_thm0, gtpm_thm, gterm_11, MEM_MAP,
             MAP_EQ1, GLAM_eq_thm0, IN_gfvl] >>
  srw_tac [][] >> metis_tac[swapstr_def, lswapstrl_apart, pmact_flip_args]);

(* tempting to delete GFV and just use supp gtpm.... *)
val GFV_supp = prove(
  ``GFV = supp gt_pmact``,
  srw_tac [][Once EQ_SYM_EQ, Once FUN_EQ_THM] >>
  match_mp_tac (GEN_ALL supp_unique_apart) >>
  srw_tac [][GFV_support, GFV_apart, FINITE_GFV]);

val gfvl_listpm = prove(
  ``gfvl = supp (list_pmact gt_pmact)``,
  srw_tac [][Once FUN_EQ_THM] >> Induct_on `x` >>
  srw_tac [][gfvl_thm, GFV_supp]);

val rmGFV = REWRITE_RULE [GFV_supp, gfvl_listpm]
val MAP_gtpm = prove(
  ``MAP (gtpm pi) l = listpm gt_pmact pi l``,
  Induct_on `l` >> srw_tac [][]);

val GLAM_eq_thm1 = REWRITE_RULE [MAP_gtpm] (SUBS [GSYM gtpm_raw] GLAM_eq_thm0)

val gtmsize_gtpml = prove(
  ``MAP gtmsize (listpm gt_pmact pi pl) = MAP gtmsize pl``,
  Induct_on `pl` >> fsrw_tac [][gtmsize_raw_gtpm, gtpm_raw]);

val gtmsize_gtpm =
  CONJ (SUBS [GSYM gtpm_raw] gtmsize_raw_gtpm) (GEN_ALL gtmsize_gtpml)

(* don't export any of these, because the intention is not to have users
   working with this type *)
val GFV_thm = save_thm("GFV_thm", rmGFV GFV_thm0)
val GFV_gtpm = save_thm("GFV_gtpm", rmGFV (SUBS [GSYM gtpm_raw] GFV_raw_gtpm))
Theorem gtpm_thm[allow_rebind] = REWRITE_RULE [MAP_gtpm] gtpm_thm
val gterm_11 = save_thm("gterm_11", gterm_11)
val GLAM_eq_thm = save_thm("GLAM_eq_thm", rmGFV GLAM_eq_thm1)
Theorem gtpm_fresh = rmGFV (SUBS [GSYM gtpm_raw] (GSYM FRESH_swap0))
val FINITE_GFV = save_thm("FINITE_GFV", rmGFV FINITE_GFV)
val IN_GFVl = save_thm("IN_GFVl", rmGFV IN_gfvl)

val _ = delete_const "gfvl"
val _ = delete_const "GFV"
val _ = delete_const "fv"

Overload GFV = ``supp gt_pmact``
Overload GFVl = ``supp (list_pmact gt_pmact)``

(* default rewriting of negations makes a mess of these. *)
Theorem  NOT_IN_GFV :
  (x ∉ GFV (GLAM v fvs bv ts us) ⇔
     ¬MEM x fvs ∧
     (∀u. MEM u us ⇒ x ∉ GFV u) ∧
     (∀t. x ≠ v ∧ MEM t ts ⇒ x ∉ GFV t))
Proof
  srw_tac [][GFV_thm, IN_GFVl] >> metis_tac []
QED

Theorem GLAM_NIL_EQ:
  GLAM u fvs1 bv1 [] ts = GLAM v fvs2 bv2 [] ts' ⇔
    fvs1 = fvs2 ∧ bv1 = bv2 ∧ ts = ts'
Proof
  srw_tac [][GLAM_eq_thm] >> metis_tac []
QED

val list_rel_split = prove(
  ``LIST_REL (λx y. P x y ∧ Q x y) l1 l2 ⇔
      LIST_REL P l1 l2 ∧ LIST_REL Q l1 l2``,
  qid_spec_tac `l2` >> Induct_on `l1` >> Cases_on `l2` >> srw_tac [][] >>
  metis_tac []);

(* generic sub-type of a generic term, where one is only allowed to look
   at the beta-value data attached to the GLAM, the number of fvs, and the
   number of arguments in the lists *)
Inductive genind:
[~lam:]
  ∀n:num v bv ts us tns uns.
     LIST_REL (genind lp) tns ts ∧
     LIST_REL (genind lp) uns us ∧
     lp n (LENGTH fvs) bv tns uns  ⇒
     genind lp n (GLAM v fvs bv ts us)
End

Theorem genind_gtpm:
  ∀n t. genind lp n t ⇒ ∀pi. genind lp n (gtpm pi t)
Proof
  Induct_on `genind` >>
  srw_tac [DNF_ss][gtpm_thm, genind_rules, list_rel_split] >>
  match_mp_tac genind_lam >>
  fsrw_tac [CONJ_ss][LIST_REL_EL_EQN,EL_MAP] >>
  srw_tac [][] >> metis_tac []
QED

Theorem genind_gtpm_eqn:
  genind lp n (gtpm pi t) = genind lp n t
Proof
  metis_tac [pmact_inverse, genind_gtpm]
QED
val _ = augment_srw_ss [rewrites [genind_gtpm_eqn]]

val LIST_REL_genind_gtpm_eqn = store_thm(
  "LIST_REL_genind_gtpm_eqn",
  ``LIST_REL (genind lp) ns (listpm gt_pmact pi ts) =
    LIST_REL (genind lp) ns ts``,
  qid_spec_tac `ns` >> Induct_on `ts` >> Cases_on `ns` >>
  fsrw_tac [][]);

val _ = augment_srw_ss [rewrites [FINITE_GFV, LIST_REL_genind_gtpm_eqn]]

Overload gtpml = ``listpm gt_pmact``

Theorem gtpml_eqr:
  !t u. (t = gtpml pi u) = (gtpml (REVERSE pi) t = u)
Proof srw_tac [][pmact_eql]
QED

Theorem genind_GLAM_eqn:
  genind lp n (GLAM v fvs bv ts us) ⇔
      ∃tns uns. LIST_REL (genind lp) tns ts ∧
                LIST_REL (genind lp) uns us ∧
                lp n (LENGTH fvs) bv tns uns
Proof
  srw_tac [DNF_ss][genind_cases, GLAM_eq_thm] >>
  srw_tac [][gtpml_eqr, perm_supp] >> metis_tac []
QED

Theorem finite_gfvl[local,simp]: FINITE (GFVl ts)
Proof Induct_on `ts` >> srw_tac [][MEM_MAP] >> srw_tac [][]
QED

Theorem bvc_genind:
  ∀P fv.
      (∀x. FINITE (fv x)) ∧
      (∀n v fvs bv tns uns ts us x.
         LIST_REL (λn t. genind lp n t ∧ ∀x. P n t x) tns ts ∧
         LIST_REL (λn t. genind lp n t ∧ ∀x. P n t x) uns us ∧
         lp n (LENGTH fvs) bv tns uns ∧ v ∉ fv x ∧
         v ∉ supp (list_pmact gt_pmact) us
        ⇒
         P n (GLAM v fvs bv ts us) x)
   ⇒
      ∀n t. genind lp n t ⇒ ∀x. P n t x
Proof
  rpt GEN_TAC >> strip_tac >>
  qsuff_tac ‘∀n t. genind lp n t ⇒ ∀pi x. P n (gtpm pi t) x’
  >- metis_tac [pmact_nil] >>
  Induct_on `genind` >> srw_tac [DNF_ss][gtpm_thm, list_rel_split] >>
  Q_TAC (NEW_TAC "z")
    ‘fv x ∪ {lswapstr pi v; v} ∪ GFVl (gtpml pi us) ∪ GFVl (gtpml pi ts) ∪
     set (listpm string_pmact pi fvs)’ >>
  ‘GLAM (lswapstr pi v) (listpm string_pmact pi fvs) bv
        (gtpml pi ts) (gtpml pi us) =
   GLAM z (listpm string_pmact pi fvs) bv
          (gtpml [(z,lswapstr pi v)] (gtpml pi ts)) (gtpml pi us)’
     by (srw_tac [][GLAM_eq_thm, NOT_IN_supp_listpm]
         >- fsrw_tac [DNF_ss][MEM_listpm_EXISTS, NOT_IN_supp_listpm,
                              GFV_gtpm] >>
         srw_tac [ETA_ss][pmact_flip_args, pmact_nil]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum match_mp_tac >>
  map_every qexists_tac [`tns`, `uns`] >>
  asm_simp_tac (srw_ss() ++ DNF_ss) [] >>
  fsrw_tac [CONJ_ss][LIST_REL_EL_EQN, EL_listpm] >>
  srw_tac [][GSYM pmact_decompose]
QED

val genindX =
    bvc_genind |> Q.SPEC `λn t x. Q n t`
               |> Q.SPEC `λx. X`
               |> SIMP_RULE (srw_ss()) []
               |> Q.INST [`Q` |-> `P`] |> GEN_ALL

val genind_KT = prove(
  ``∀n t. genind (λn lfvs bv tns uns. T) n t``,
  CONV_TAC SWAP_FORALL_CONV >> ho_match_mp_tac simple_induction >>
  srw_tac [][] >>
  match_mp_tac genind_lam >>
  map_every qexists_tac [`GENLIST (K 0) (LENGTH bndts)`,
                         `GENLIST (K 0) (LENGTH unbndts)`] >>
  fsrw_tac[DNF_ss] [LIST_REL_EL_EQN, MEM_EL]);

val vacuous_list_rel = prove(
  ``LIST_REL (λx y. P y) xs ys ⇔
     (∀y. MEM y ys ⇒ P y) ∧ (LENGTH xs = LENGTH ys)``,
  qid_spec_tac `ys` >> Induct_on `xs` >> Cases_on `ys` >> srw_tac [][] >>
  metis_tac []);

val silly = prove(
  ``(∀v fvs bv tns uns ts us x.
       LIST_REL (λn:num t. ∀x. Q t x) tns ts ∧
       LIST_REL (λn:num t. ∀x. Q t x) uns us ∧ v ∉ fv x ∧
       v ∉ supp (list_pmact gt_pmact) us ⇒
       Q (GLAM v fvs bv ts us) x) ⇔
   (∀v fvs bv ts us x.
      (∀t x. MEM t ts ⇒ Q t x) ∧ (∀u x. MEM u us ⇒ Q u x) ∧
      v ∉ fv x ∧ v ∉ supp (list_pmact gt_pmact) us ⇒
      Q (GLAM v fvs bv ts us) x)``,
  srw_tac [][EQ_IMP_THM, vacuous_list_rel] >>
  first_x_assum (Q.SPECL_THEN [`v`,‘fvs’, `bv`,`GENLIST (K 0) (LENGTH ts)`,
                               `GENLIST (K 0) (LENGTH us)`] MP_TAC) >>
  srw_tac [][]);

val gen_bvc_induction =
    bvc_genind |> SPEC_ALL
               |> Q.INST [`lp` |-> `(λn lfvs bv tns uns. T)`,
                          `vp` |-> `(λn vv. T)`,
                          `P` |-> `λn t x. Q t x`]
               |> SIMP_RULE (srw_ss()) [genind_KT, silly]
               |> Q.INST [`Q` |-> `P`] |> GEN_ALL

val bvc_ind =
    gen_bvc_induction |> INST_TYPE [gamma |-> ``:one``]
                      |> SPEC_ALL
                      |> Q.INST [`P` |-> `λt x. Q t`, `fv` |-> `λx. X`]
                      |> SIMP_RULE (srw_ss()) []
                      |> Q.INST [`Q` |-> `P`]
                      |> Q.GEN `X` |> Q.GEN `P`

Theorem gterm_cases:
  ∀t. ∃s fvs bv ts us. t = GLAM s fvs bv ts us
Proof
  ho_match_mp_tac simple_induction >>
  srw_tac [][] >> metis_tac []
QED

Theorem FORALL_gterm:
  (∀t. P t) ⇔ (∀s fvs bv ts us. P (GLAM s fvs bv ts us))
Proof
  EQ_TAC >> srw_tac [][] >>
  qspec_then `t` STRUCT_CASES_TAC gterm_cases >> srw_tac [][]
QED

val some_5_F = prove(
  ``(some (v,w,x,y,z). F) = NONE``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

Theorem SUM_MAP_MEM:
  ∀f x l. MEM x l ⇒ f x ≤ SUM (MAP f l)
Proof
  ntac 2 gen_tac >> Induct >> srw_tac [][] >>
  fsrw_tac [ARITH_ss][]
QED

val lf = mk_var ("lf", “: string -> string list -> α ->
                           (ρ -> γ) list -> (ρ -> γ) list
                           -> α gterm list -> α gterm list -> ρ -> γ”)

val trec = “tmrec (A: string set) (ppm: ρ pmact) ^lf : α gterm -> ρ -> γ”

Definition tmrec_def:
  ^trec t = λp.
    case some(v,fvs,bv,ts,us).
           t = GLAM v fvs bv ts us ∧ v ∉ supp ppm p ∧ v ∉ GFVl us ∧ v ∉ A ∧
           ¬MEM v fvs
    of
      SOME (v,fvs,bv,ts,us) =>
        lf v fvs bv (MAP (^trec) ts) (MAP (^trec) us) ts us p
    | NONE => ARB
Termination
  WF_REL_TAC `measure (gtmsize o SND o SND o SND)` >>
  srw_tac [][] >>
  qspec_then `t` FULL_STRUCT_CASES_TAC gterm_cases >>
  fsrw_tac [][some_5_F] >>
  fsrw_tac [][GLAM_eq_thm] >>
  qpat_x_assum `X = SOME Y` mp_tac >>
  DEEP_INTRO_TAC optionTheory.some_intro >>
  simp_tac (srw_ss()) [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] >>
  srw_tac [][gtmsize_thm] >>
  Q.ISPEC_THEN `gtmsize` imp_res_tac SUM_MAP_MEM >>
  srw_tac [][gtmsize_gtpm] >>
  DECIDE_TAC
End

val lp = ``lp: num -> num -> α -> num list -> num list -> bool``

Overload "→"[local] = ``fnpm``
val _ = temp_set_fixity "→" (Infixr 700)

val relsupp_def = Define`
  relsupp A dpm ppm t r <=>
    ∀x. x ∉ A ∧ x ∉ GFV t ==> x ∉ supp (fn_pmact ppm dpm) r
`;

Definition sidecond_def:
  sidecond dpm ppm A ^lp ^lf ⇔
  FINITE A ∧ (∀p. FINITE (supp ppm p)) ∧
    (∀x y n v fvs bv r1 r2 ts us p.
       x ∉ A ∧ y ∉ A ∧ v ∉ A ∧
       genind lp n (GLAM v fvs bv ts us) ∧
       LIST_REL (relsupp A dpm ppm) ts r1 ∧
       LIST_REL (relsupp A dpm ppm) us r2 ∧
       v ∉ supp ppm p ⇒
       (pmact dpm [(x,y)] (^lf v fvs bv r1 r2 ts us p) =
        ^lf (lswapstr [(x,y)] v)
            (listpm string_pmact [(x,y)] fvs)
            bv
            (listpm (fn_pmact ppm dpm) [(x,y)] r1)
            (listpm (fn_pmact ppm dpm) [(x,y)] r2)
            (listpm gt_pmact [(x,y)] ts)
            (listpm gt_pmact [(x,y)] us)
            (pmact ppm [(x,y)] p)))
End

val FCB_def = Define`
  FCB dpm ppm A ^lp ^lf ⇔
  ∀a n v fvs bv r1 r2 ts us p.
     a ∉ A ∧ a ∉ GFVl us ∧ a ∉ supp ppm p ∧
     ¬MEM a fvs ∧
     LIST_REL (relsupp A dpm ppm) ts r1 ∧
     LIST_REL (relsupp A dpm ppm) us r2 ∧
     genind lp n (GLAM v fvs bv ts us) ⇒
     a ∉ supp dpm (^lf a fvs bv r1 r2 ts us p)`

val some_2_EQ = prove(
  ``(some (x,y). (x' = x) /\ (y' = y)) = SOME(x',y')``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

val some_2_F = prove(
  ``(some (x,y). F) = NONE``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

val tmrec_GLAM = tmrec_def |> SPEC_ALL |> Q.INST [`t` |-> `GLAM v fvs bv ts us`]
  |> SIMP_RULE (srw_ss()) [some_2_F,NOT_IN_supp_listpm]
  |> C (foldr (uncurry Q.GEN)) [`v`,‘fvs’, `bv`,`ts`,`us`]

Theorem gtpm_eqr:
  (t = gtpm pi u) = (gtpm (REVERSE pi) t = u)
Proof METIS_TAC [pmact_inverse]
QED

val lswapstr_sing = Q.prove(`lswapstr [(x,y)] z = swapstr x y z`, srw_tac [][]);

val trec_fnpm = prove(
  ``(ppm → apm) π (tmrec A ppm vf lf t) =
    λp. pmact apm π (tmrec A ppm vf lf t (pmact ppm π⁻¹ p))``,
  srw_tac [][FUN_EQ_THM, fnpm_def]);

Theorem MAP_trec_fnpm[local]:
  MAP ((ppm → dpm) pi o tmrec A ppm vf lf) =
  MAP (λt p. pmact dpm pi (tmrec A ppm vf lf t (pmact ppm (REVERSE pi) p)))
Proof
  ONCE_REWRITE_TAC [FUN_EQ_THM] >>
  Induct >> srw_tac [][trec_fnpm]
QED

Theorem genind_GLAM_subterm:
  genind lp n (GLAM v fvs bv ts us) ∧ (MEM u ts ∨ MEM u us) ⇒
  ∃n. genind lp n u
Proof
  srw_tac [][Once genind_cases] >>
  fsrw_tac [][GLAM_eq_thm] >>
  fsrw_tac [][LIST_REL_EL_EQN,MEM_EL] >>
  srw_tac [][] >>
  fsrw_tac [][EL_MAP] >>
  metis_tac []
QED

val gtmsize_GLAM_subterm = store_thm(
"gtmsize_GLAM_subterm",
``(MEM t ts ∨ MEM t us) ⇒ gtmsize t < gtmsize (GLAM s fvs bv ts us)``,
srw_tac [][gtmsize_thm] >>
imp_res_tac SUM_MAP_MEM >>
pop_assum (qspec_then `gtmsize` mp_tac) >>
DECIDE_TAC);

Theorem LIST_REL_relsupp_gtpml[local]:
  ∀A dpm ppm l1 l2.
      LIST_REL (relsupp A dpm ppm) l1 l2 ==>
      ∀x y. x ∉ A ∧ y ∉ A ==>
         LIST_REL (relsupp A dpm ppm)
                  (gtpml [(x,y)] l1)
                  (listpm (fn_pmact ppm dpm) [(x,y)] l2)
Proof
  ntac 3 gen_tac >>
  Induct_on `LIST_REL` >> srw_tac [][relsupp_def, fnpm_def, perm_supp] >>
  first_x_assum match_mp_tac >> srw_tac [][perm_supp] >>
  srw_tac [][swapstr_def]
QED

fun ih_commute_tac dir (asl,w) =
    first_x_assum (fn rwt =>
         if free_in ``gtmsize`` (concl rwt) then
           mp_tac (Q.GEN `n'` (PART_MATCH (lhs o #2 o strip_imp) rwt (dir w)))
         else NO_TAC) (asl,w)

fun sidecond_tac dir =
  qpat_x_assum `sidecond AA BB CC DD EE `
     (fn th => th |> SIMP_RULE (srw_ss()) [sidecond_def] |> CONJUNCTS
                  |> last |> (fn th' => assume_tac th >> assume_tac th')) >>
  (fn (asl,w) =>
    pop_assum (fn rwt => mp_tac (PART_MATCH (lhs o #2 o strip_imp)
                                            rwt
                                            (dir w))) (asl,w))

val listpm_tMAP = prove(
  ``(listpm apm pi (MAP f l) =
     MAP ((gt_pmact → apm) pi f) (gtpml pi l))``,
  srw_tac [][] >> Induct_on `l` >> srw_tac [][fnpm_def]);

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

Theorem genind_ignores_fvspm:
  genind lp n (GLAM v (listpm string_pmact pi fvs) bv ts us) ⇔
  genind lp n (GLAM v fvs bv ts us)
Proof
  simp[genind_GLAM_eqn]
QED

Theorem tmrec_equivariant:
  sidecond dpm ppm A ^lp ^lf ∧ FCB dpm ppm A ^lp ^lf ⇒
  ∀n. genind lp n t ⇒
      ∀p x y. x ∉ A ∧ y ∉ A ⇒
              (pmact dpm [(x,y)] (tmrec A ppm lf t p) =
               tmrec A ppm lf (gtpm [(x,y)] t) (pmact ppm [(x,y)] p))
Proof
  strip_tac >>
  completeInduct_on ‘gtmsize t’ >>
  qabbrev_tac ‘m = v’ >> markerLib.RM_ALL_ABBREVS_TAC >>
  pop_assum (strip_assume_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  simp_tac (srw_ss()) [Once FORALL_gterm] >>
  rpt gen_tac >>
  disch_then SUBST_ALL_TAC >>
  gen_tac >> strip_tac >>
  qx_gen_tac ‘p’ >>
  Q.SPECL_THEN [‘s’,‘fvs’, ‘bv’,‘ts’,‘us’,‘p’] MP_TAC
   (tmrec_GLAM |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]) >>
  DEEP_INTRO_TAC optionTheory.some_intro >>
  asm_simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  ‘FINITE A ∧ (∀p. FINITE (supp ppm p))’
    by fsrw_tac [][sidecond_def] >>
  reverse conj_tac >- (
  (* bogus some(...) = ARB case *)
  Q_TAC (NEW_TAC "z") ‘supp ppm p ∪ A ∪ GFVl us ∪ GFVl ts ∪ {s} ∪ set fvs’ >>
  disch_then (qspec_then ‘z’ mp_tac) >>
  asm_simp_tac (srw_ss()++DNF_ss)
               [GLAM_eq_thm,IN_GFVl,gtpml_eqr,listpm_MAP,MEM_MAP,GFV_gtpm] >>
  fsrw_tac [][IN_GFVl] >>
  metis_tac []) >>
  map_every qx_gen_tac [‘s'’,‘fvs'’, ‘bv'’,‘ts'’,‘us'’] >>
  strip_tac >>
  strip_tac >>
  ‘fvs' = fvs ∧ us' = us ∧ bv' = bv’
    by fsrw_tac [][GLAM_eq_thm] >> rpt VAR_EQ_TAC >>
  asm_simp_tac (srw_ss()++DNF_ss) [gtpm_thm,IN_GFVl,GFV_thm] >>
  map_every qx_gen_tac [‘x’, ‘y’] >>
  strip_tac >>
  qpat_x_assum ‘tmrec A ppm lf (GLAM X _ Y Z WW) p = XX’ (K ALL_TAC) >>
  srw_tac [][tmrec_GLAM] >>
  DEEP_INTRO_TAC optionTheory.some_intro >>
  asm_simp_tac (srw_ss()++ETA_ss) [pairTheory.FORALL_PROD] >>
  reverse conj_tac >- (
  (* bogus ARB case *)
  asm_simp_tac (srw_ss()) [GLAM_eq_thm] >>
  Q_TAC (NEW_TAC "z")
        ‘{swapstr x y s'} ∪ A ∪ supp ppm (pmact ppm [(x,y)] p) ∪
         GFVl (gtpml [(x,y)] us) ∪ GFVl (gtpml [(x,y)] ts') ∪
         set (listpm string_pmact [(x,y)] fvs)’ >>
  disch_then (qspec_then ‘z’ mp_tac) >>
  fsrw_tac [DNF_ss][IN_GFVl,gtpml_eqr,listpm_MAP,MEM_MAP,GFV_gtpm] >>
  reverse conj_tac >- metis_tac [] >>
  conj_tac >- metis_tac [] >>
  srw_tac [][] >> metis_tac []) >>
  qabbrev_tac ‘r1 = MAP (tmrec A ppm lf) ts'’ >>
  qabbrev_tac ‘r2 = MAP (tmrec A ppm lf) us’ >>
  fsrw_tac [][AND_IMP_INTRO] >>
  ‘∃tns uns. LIST_REL (genind lp) tns ts ∧ LIST_REL (genind lp) uns us’
    by (fsrw_tac [][genind_cases, GLAM_eq_thm] >> srw_tac [][] >>
        metis_tac []) >>
  ‘LIST_REL (genind lp) tns ts'’
    by (fsrw_tac [][GLAM_eq_thm] >> srw_tac [][] >> fsrw_tac [][]) >>
  qabbrev_tac ‘GGSIZE = gtmsize (GLAM s' fvs bv ts' us)’ >>
  ‘∀t n' a. gtmsize t < GGSIZE ∧ genind lp n' t ∧ a ∉ A ∧ a ∉ GFV t ==>
            a ∉ supp (fn_pmact ppm dpm) (tmrec A ppm lf t)’
    by (srw_tac [][] >> match_mp_tac notinsupp_I >>
        qexists_tac ‘A ∪ GFV t’ >>
        srw_tac [][support_def, fnpm_def, FUN_EQ_THM] >>
        metis_tac [supp_fresh, pmact_sing_inv]) >>
  ‘LIST_REL (relsupp A dpm ppm) ts' r1 ∧ LIST_REL (relsupp A dpm ppm) us r2’
    by (srw_tac [][LIST_REL_EL_EQN, relsupp_def, Abbr‘r1’, Abbr‘r2’] >>
        srw_tac [][EL_MAP] >> first_x_assum match_mp_tac >|
        [qexists_tac ‘EL n' tns’, qexists_tac ‘EL n' uns’] >>
        metis_tac [LIST_REL_EL_EQN, MEM_EL, gtmsize_GLAM_subterm]) >>
  (* COMPLETE THIS... *)
  ‘∀t p x y.
     (MEM t ts' ∨ MEM t us ∨ MEM t ts) ∧ x ∉ A ∧ y ∉ A ==>
     (pmact dpm [(x,y)] (tmrec A ppm lf t p) =
      tmrec A ppm lf (gtpm [(x,y)] t) (pmact ppm [(x,y)] p))’
    by (srw_tac [][] >> first_x_assum match_mp_tac >>
        fsrw_tac [][GLAM_eq_thm] >> srw_tac [][] >>
        fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
        metis_tac [genind_GLAM_subterm, gtmsize_GLAM_subterm]) >>
  (* THEN COMPLETE THIS ... *)
  ‘(∀a b. a ∉ A ∧ b ∉ A ==>
          (listpm (fn_pmact ppm dpm) [(a,b)] r1 =
           MAP (tmrec A ppm lf) (gtpml [(a,b)] ts'))) ∧
   (∀a b. a ∉ A ∧ b ∉ A ==>
          (listpm (fn_pmact ppm dpm) [(a,b)] r2 =
           MAP (tmrec A ppm lf) (gtpml [(a,b)] us)))’
    by (asm_simp_tac (srw_ss() ++ DNF_ss)
                     [listpm_tMAP, MAP_EQ_f, MEM_listpm_EXISTS,
                      Abbr‘r1’, Abbr‘r2’, fnpm_def, FUN_EQ_THM,
                      pmact_sing_inv]) >>
  map_every qx_gen_tac [‘s''’, ‘fvs'’, ‘bv'’, ‘ts''’, ‘us'’] >>
  srw_tac [][] >>
  ‘fvs' = listpm string_pmact [(x,y)] fvs ∧ bv' = bv ∧ us' = gtpml [(x,y)] us’
    by fsrw_tac [][GLAM_eq_thm] >>
  rpt VAR_EQ_TAC >>
  sidecond_tac lhs >>
  disch_then (fn th => asm_simp_tac (srw_ss()) [th]) >>
  qpat_x_assum ‘GLAM (swapstr x y s') _ bv Z1 Z2 = Z3’ mp_tac >>
  srw_tac [][GLAM_eq_thm] >>
  qabbrev_tac ‘u = swapstr x y s'’ >>
  fsrw_tac [][gtpml_eqr] >>
  qpat_x_assum ‘XX = ts''’ (SUBST_ALL_TAC o SYM) >>
  ‘u ∉ A’ by srw_tac [][Abbr‘u’,swapstr_def] >>
  ‘u ∉ supp ppm (pmact ppm [(x,y)] p)’ by srw_tac [][Abbr‘u’,perm_supp] >>
  ‘s'' ∉ supp (list_pmact gt_pmact) (gtpml [(x,y)] us) ∧
   s'' ∉ supp (list_pmact gt_pmact) (gtpml [(x,y)] ts')’ by (
    fsrw_tac [DNF_ss][IN_GFVl,listpm_MAP,MEM_MAP,GFV_gtpm] >>
    metis_tac [] ) >>
  ‘u ∉ supp (list_pmact gt_pmact) (gtpml [(x,y)] us)’ by (
    fsrw_tac [DNF_ss][IN_GFVl,listpm_MAP,MEM_MAP,GFV_gtpm,Abbr‘u’] >>
    metis_tac [] ) >>
  ‘genind lp n
   (GLAM u (listpm string_pmact[(x,y)] fvs) bv
         (gtpml [(x,y)] ts') (gtpml [(x,y)] us))’ by (
    qmatch_abbrev_tac ‘genind lp n t’ >>
    qsuff_tac ‘t = gtpm [(x,y)] (GLAM s' fvs bv ts' us)’ >- srw_tac [][] >>
    srw_tac [][Abbr‘t’,gtpm_thm] ) >>
  qmatch_abbrev_tac ‘LHS = RHS’ >>
  match_mp_tac EQ_TRANS >>
  qexists_tac ‘pmact dpm [(u,s'')] RHS’ >>
  qabbrev_tac ‘usxyts = gtpml [(u,s'')] (gtpml [(x,y)] ts')’ >>
  qabbrev_tac ‘xyus = gtpml [(x,y)] us’ >>
  qabbrev_tac ‘usxyfvs = listpm string_pmact [(u,s'')] $
                                listpm string_pmact [(x,y)] fvs’ >>
  ‘genind lp n (GLAM s'' usxyfvs bv usxyts xyus)’
    by(first_x_assum (mp_tac o MATCH_MP genind_gtpm) >>
       disch_then (qspec_then ‘[(u,s'')]’ mp_tac) >>
       CONV_TAC (LAND_CONV (RAND_CONV (REWRITE_CONV [gtpm_thm]))) >>
       asm_simp_tac (srw_ss()) [supp_fresh]) >>
  ‘genind lp n (GLAM s'' fvs bv usxyts xyus)’
    by gvs[Abbr‘usxyfvs’, genind_ignores_fvspm] >>
  ‘LIST_REL (relsupp A dpm ppm) usxyts (MAP (tmrec A ppm lf) usxyts) ∧
   LIST_REL (relsupp A dpm ppm) xyus (MAP (tmrec A ppm lf) xyus)’
    by (map_every qunabbrev_tac [‘r1’, ‘r2’, ‘usxyts’, ‘xyus’] >>
        rpt (first_x_assum (mp_tac o MATCH_MP LIST_REL_relsupp_gtpml)) >>
        rpt (disch_then (qspecl_then [‘x’,‘y’] assume_tac)) >>
        ntac 2 (pop_assum mp_tac) >> asm_simp_tac (srw_ss()) [] >>
        rpt (disch_then (assume_tac o MATCH_MP LIST_REL_relsupp_gtpml)) >>
        ntac 2 (pop_assum (qspecl_then [‘u’, ‘s''’] mp_tac)) >>
        asm_simp_tac (srw_ss()) [listpm_tMAP] >>
        rpt (disch_then assume_tac) >>
        qpat_x_assum ‘LIST_REL _ (_ (_ ts')) (MAP _ _)’ mp_tac >>
        qmatch_abbrev_tac
        ‘LIST_REL RR TS (MAP f1 TS) ==> LIST_REL RR TS (MAP f2 TS)’ >>
        qsuff_tac ‘MAP f1 TS = MAP f2 TS’ >- srw_tac [][] >>
        srw_tac [][MAP_EQ_f] >>
        map_every qunabbrev_tac [‘f1’, ‘f2’, ‘TS’] >>
        asm_simp_tac (srw_ss()) [FUN_EQ_THM, fnpm_def] >> gen_tac >>
        ih_commute_tac lhs >> asm_simp_tac (srw_ss()) [pmact_sing_inv] >>
        disch_then match_mp_tac >>
        fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
        metis_tac [gtmsize_GLAM_subterm, genind_GLAM_subterm]) >>
  reverse conj_tac >- (
  match_mp_tac supp_fresh >>
  reverse conj_tac >- (
    fsrw_tac [][FCB_def,Abbr‘RHS’] >>
    first_x_assum match_mp_tac >>
    asm_simp_tac (srw_ss()) [] >>
    map_every qexists_tac [‘n’,‘s''’] >>
    srw_tac [][genind_ignores_fvspm]) >>
  match_mp_tac notinsupp_I >>
  qunabbrev_tac ‘RHS’ >>
  qexists_tac
  ‘A ∪ {s''} ∪ supp ppm (pmact ppm [(x,y)] p) ∪
   set (listpm string_pmact [(x,y)] fvs) ∪ GFVl xyus ∪ GFVl usxyts’ >>
  ‘FINITE A ∧ (∀p. FINITE (supp ppm p))’ by fsrw_tac [][sidecond_def] >>
  asm_simp_tac (srw_ss()) [support_def] >> reverse conj_tac
  >- simp[MEM_listpm, Abbr‘u’] >>
  map_every qx_gen_tac [‘w’,‘z’] >>
  strip_tac >>
  sidecond_tac lhs >> impl_tac
  >- simp[genind_ignores_fvspm] >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (K ALL_TAC) >>
  asm_simp_tac (srw_ss()) [listpm_tMAP, supp_fresh] >>
  rpt AP_THM_TAC >>
  qmatch_abbrev_tac ‘lf s'' FVS1 bv X1 Y1 = lf s'' FVS2 bv X2 Y2’ >>
  qsuff_tac ‘FVS1 = FVS2 ∧ X1 = X2 ∧ Y1 = Y2’ >- srw_tac [][] >>
  map_every qunabbrev_tac [‘X1’, ‘X2’, ‘Y1’, ‘Y2’, ‘FVS1’, ‘FVS2’] >>
  asm_simp_tac (srw_ss() ++ DNF_ss)
               [MAP_EQ_f, MEM_listpm_EXISTS, FUN_EQ_THM, fnpm_def] >>
  conj_tac
  >- (irule supp_fresh >> simp[IN_supp_listpm]) >>
  srw_tac [][] >> (* two similar goals here-on *)
  ih_commute_tac lhs >>
  asm_simp_tac (srw_ss()) [gtmsize_gtpm, pmact_sing_inv] >>
  disch_then match_mp_tac >>
  map_every qunabbrev_tac [‘usxyts’, ‘xyus’] >>
  fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
  metis_tac [gtmsize_GLAM_subterm, genind_GLAM_subterm]) >>
  srw_tac [][Abbr‘RHS’] >>
  sidecond_tac rhs >> impl_tac >- simp[genind_ignores_fvspm] >>
  asm_simp_tac (srw_ss()) [listpm_tMAP, supp_fresh] >>
  disch_then (K ALL_TAC) >>
  qunabbrev_tac ‘LHS’ >> rpt AP_THM_TAC >>
  qunabbrev_tac ‘usxyts’ >>
  asm_simp_tac (srw_ss() ++ ETA_ss) [pmact_sing_inv, pmact_nil] >>
  AP_THM_TAC >>
  qmatch_abbrev_tac ‘lf u FVS1 bv X1 Y1 = lf u FVS2 bv X2 Y2’ >>
  qsuff_tac ‘FVS1 = FVS2 ∧ X1 = X2 ∧ Y1 = Y2’ >- srw_tac [][] >>
  map_every qunabbrev_tac [‘X1’,‘X2’,‘Y1’, ‘Y2’, ‘FVS1’, ‘FVS2’] >>
  conj_tac
  >- (simp[Abbr‘usxyfvs’] >> sym_tac >> irule supp_fresh >>
      simp[IN_supp_listpm] >> simp[MEM_listpm, Abbr‘u’]) >>
  conj_tac >> (* splits in two *)
  srw_tac [][MAP_EQ_f, FUN_EQ_THM, fnpm_def] >>
  ih_commute_tac rhs >>
  asm_simp_tac (srw_ss()) [pmact_sing_inv, gtmsize_gtpm] >>
  disch_then (match_mp_tac o GSYM) >>
  qunabbrev_tac ‘xyus’ >>
  fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
  metis_tac [genind_GLAM_subterm, gtmsize_GLAM_subterm]
QED

fun udplus th =
    th |> REWRITE_RULE [GSYM CONJ_ASSOC]
       |> repeat (UNDISCH o CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)))
       |> UNDISCH

val eqv_I = tmrec_equivariant |> udplus

Theorem tmrec_fresh:
  sidecond dpm ppm A ^lp ^lf ∧ FCB dpm ppm A lp lf ==>
    ∀n t. genind lp n t ==>
          ∀x. x ∉ A ∧ x ∉ GFV t ==>
              x ∉ supp (fn_pmact ppm dpm) (tmrec A ppm lf t)
Proof
  srw_tac [][] >> match_mp_tac notinsupp_I >> qexists_tac `GFV t ∪ A` >>
  `FINITE A` by fsrw_tac [][sidecond_def] >>
  srw_tac [][support_def, FUN_EQ_THM, fnpm_def] >>
  metis_tac [tmrec_equivariant, supp_fresh, pmact_sing_inv]
QED

Definition NEWFCB_def:
  NEWFCB dpm ppm A lp lf ⇔
  ∀a1 a2 n fvs bv r1 r2 ts us p.
     a1 ∉ A ∧ a1 ∉ supp ppm p ∧ a2 ∉ A ∧ a2 ∉ GFVl ts ∧ a2 ∉ supp ppm p ∧
     LIST_REL (relsupp A dpm ppm) ts r1 ∧
     LIST_REL (relsupp A dpm ppm) us r2 ∧
     genind lp n (GLAM a1 fvs bv ts us) ==>
     (lf a2 fvs bv (listpm (fn_pmact ppm dpm) [(a2,a1)] r1) r2
               (gtpml [(a2,a1)] ts) us p =
      lf a1 fvs bv r1 r2 ts us p)
End

Theorem LIST_REL_combined_supps[local]:
  LIST_REL (relsupp A dpm ppm) ts rs ∧ x ∉ A ∧ x ∉ GFVl ts ==>
  x ∉ supp (list_pmact (fn_pmact ppm dpm)) rs
Proof
  qsuff_tac
    `∀ts rs. LIST_REL (relsupp A dpm ppm) ts rs ==>
             ∀x. x ∉ GFVl ts ∧ x ∉ A ==> x ∉ supp (list_pmact (fn_pmact ppm dpm)) rs`
    >- metis_tac [] >>
  Induct_on `LIST_REL` >> srw_tac [][relsupp_def]
QED

Theorem NEWFCB_OLD:
  NEWFCB dpm ppm A lp ^lf ∧ sidecond dpm ppm A lp lf ==>
  FCB dpm ppm A lp lf
Proof
  srw_tac [][FCB_def, NEWFCB_def] >>
  ‘FINITE A ∧ (∀p. FINITE (supp ppm p))’
     by fsrw_tac [][sidecond_def] >>
  Q_TAC (NEW_TAC "z") ‘A ∪ GFVl ts ∪ GFVl us ∪ supp ppm p ∪ {a} ∪ set fvs’ >>
  ‘lf a fvs bv r1 r2 ts us p =
   lf z fvs bv (listpm (fn_pmact ppm dpm) [(z,a)] r1) r2
      (gtpml [(z,a)] ts) us p’
     by (fsrw_tac [][NEWFCB_def] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
         first_x_assum match_mp_tac >>
         fsrw_tac [][genind_GLAM_eqn] >> metis_tac []) >>
  pop_assum SUBST1_TAC >>
  match_mp_tac notinsupp_I >>
  qexists_tac ‘{z} ∪ A ∪ GFVl (gtpml [(z,a)] ts) ∪ GFVl us ∪ supp ppm p ∪
              set fvs’ >>
  srw_tac [][perm_supp]>>
  srw_tac [][support_def] >>
  sidecond_tac lhs >>
  ‘x ∉ supp (list_pmact (fn_pmact ppm dpm)) r2 ∧
   y ∉ supp (list_pmact (fn_pmact ppm dpm)) r2 ∧
   x ∉ supp (list_pmact (fn_pmact ppm dpm))
            (listpm (fn_pmact ppm dpm) [(z,a)] r1) ∧
   y ∉ supp (list_pmact (fn_pmact ppm dpm))
            (listpm (fn_pmact ppm dpm) [(z,a)] r1)’
    by (srw_tac [][perm_supp] >>
        metis_tac [LIST_REL_combined_supps, swapstr_def]) >>
  asm_simp_tac (srw_ss()) [LIST_REL_relsupp_gtpml, genind_GLAM_eqn, supp_fresh,
                           perm_supp] >>
  ‘listpm string_pmact [(x,y)] fvs = fvs’
    by (irule supp_fresh >> simp[IN_supp_listpm]) >> simp[] >>
  disch_then match_mp_tac >> fsrw_tac [][genind_GLAM_eqn] >> metis_tac []
QED

val fresh_I = PROVE_HYP (udplus NEWFCB_OLD) (udplus tmrec_fresh)
val eqv_I = PROVE_HYP (udplus NEWFCB_OLD) (udplus tmrec_equivariant)


fun xmatch_cond_assum dir (asl,w) =
    first_x_assum (fn rwt =>
       mp_tac (PART_MATCH (lhs o #2 o strip_imp)
                          rwt
                          (dir w))) (asl,w)

Theorem parameter_gtm_recursion:
  sidecond dpm ppm A ^lp ^lf ∧ NEWFCB dpm ppm A ^lp ^lf ⇒
  ∃f.
    (∀n v fvs bv ns ms ts us p.
       v ∉ A ∧ v ∉ supp ppm p ∧ genind lp n (GLAM v fvs bv ts us) ⇒
       (f (GLAM v fvs bv ts us) p = lf v fvs bv (MAP f ts) (MAP f us) ts us p)) ∧
    ∀n t p.
      genind lp n t ==>
      ∀x y. x ∉ A ∧ y ∉ A ==>
            pmact dpm [(x,y)] (f t p) =
            f (gtpm [(x,y)] t) (pmact ppm [(x,y)] p)
Proof
  strip_tac >>
  ‘FINITE A ∧ ∀p. FINITE (supp ppm p)’ by fsrw_tac [][sidecond_def] >>
  qexists_tac ‘tmrec A ppm lf’ >>
  reverse conj_tac
  >- (rpt strip_tac >> imp_res_tac eqv_I >> srw_tac [][]) >>
  srw_tac [][tmrec_GLAM] >>
  DEEP_INTRO_TAC optionTheory.some_intro >>
  asm_simp_tac (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
  reverse conj_tac
  >- ((* bogus ARB case *)
      asm_simp_tac (srw_ss()) [GLAM_eq_thm] >>
      Q_TAC (NEW_TAC "z") ‘A ∪ supp ppm p ∪ GFVl ts ∪ GFVl us ∪ {v} ∪ set fvs’ >>
      disch_then (qspec_then ‘z’ mp_tac) >>
      fsrw_tac [][gtpml_eqr] >>
      fsrw_tac [DNF_ss][IN_supp_listpm, MEM_listpm_EXISTS, perm_supp] >>
      metis_tac []) >>
  asm_simp_tac (srw_ss()++DNF_ss++ETA_ss) [GLAM_eq_thm,gtpml_eqr,gtpm_eqr] >>
  qx_gen_tac ‘u’ >> strip_tac >>
  ‘LIST_REL (relsupp A dpm ppm) ts (MAP (tmrec A ppm lf) ts) ∧
   LIST_REL (relsupp A dpm ppm) us (MAP (tmrec A ppm lf) us)’
    by (assume_tac fresh_I >>
        fsrw_tac [DNF_ss][MEM_EL] >>
        srw_tac [][LIST_REL_EL_EQN, EL_MAP, relsupp_def] >>
        fsrw_tac [][AND_IMP_INTRO] >>
        first_x_assum match_mp_tac >>
        fsrw_tac [][] >>
        match_mp_tac genind_GLAM_subterm >>
        srw_tac [][MEM_EL] >>
        metis_tac []) >>
  asm_simp_tac (srw_ss()) [pmact_flip_args] >>
  qsuff_tac ‘MAP (tmrec A ppm lf) (gtpml [(u,v)] ts) =
             listpm (fn_pmact ppm dpm) [(u,v)] (MAP (tmrec A ppm lf) ts)’
  >- (disch_then SUBST1_TAC >> fsrw_tac [][NEWFCB_def] >>
      first_x_assum match_mp_tac >> fsrw_tac [][perm_supp] >> metis_tac []) >>
  srw_tac [][listpm_tMAP, MAP_EQ_f, MEM_listpm_EXISTS, FUN_EQ_THM, fnpm_def] >>
  srw_tac [][pmact_sing_inv] >>
  assume_tac (eqv_I |> Q.GEN ‘t’
                    |> SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]) >>
  (fn (asl,w) => pop_assum
                 (fn rwt =>
                    mp_tac (PART_MATCH (lhs o #2 o dest_imp) rwt
                                       (rhs w) |> Q.GEN ‘n’)) (asl,w)) >>
  asm_simp_tac (srw_ss()) [pmact_sing_inv] >>
  metis_tac [genind_GLAM_subterm]
QED

val _ = export_theory()
