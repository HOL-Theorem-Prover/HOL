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

val _ = Datatype `
  pregterm = var string 'v
           | lam string 'b (pregterm list) (pregterm list)
`;

val fv_def = Define `
  (fv (var s vv) = {s}) ∧
  (fv (lam v bv bndts unbndts) = (fvl bndts DELETE v) ∪ fvl unbndts) ∧
  (fvl [] = ∅) ∧
  (fvl (h::ts) = fv h ∪ fvl ts)`
val _ = augment_srw_ss [rewrites [fv_def]]

val oldind = TypeBase.induction_of ``:(α,β)pregterm``

val pind = prove(
  ``∀P.
      (∀s vv. P (var s vv)) ∧
      (∀v bv bndts unbndts.
         EVERY P bndts ∧ EVERY P unbndts ⇒ P (lam v bv bndts unbndts))
    ⇒
      ∀t. P t``,
  gen_tac >> strip_tac >>
  Q_TAC suff_tac `(∀t. P t) ∧ (∀ts. EVERY P ts)` >- metis_tac [] >>
  ho_match_mp_tac oldind >> srw_tac [][]);

val finite_fv = store_thm(
  "finite_fv",
  ``∀t. FINITE (fv t)``,
  Q_TAC suff_tac `(∀t:(α,β)pregterm. FINITE (fv t)) ∧
                  (∀l:(α,β)pregterm list. FINITE (fvl l))` >- srw_tac [][] >>
  ho_match_mp_tac oldind >> srw_tac [][]);
val _ = augment_srw_ss [rewrites [finite_fv]]

val raw_ptpm_def = Define`
  (raw_ptpm p (var s vv) = var (lswapstr p s) vv) ∧
  (raw_ptpm p (lam v bv bndts unbndts) = lam (lswapstr p v)
                                         bv
                                         (raw_ptpml p bndts)
                                         (raw_ptpml p unbndts)) ∧
  (raw_ptpml p [] = []) ∧
  (raw_ptpml p (h::t) = raw_ptpm p h :: raw_ptpml p t)
`;

val _ = overload_on("pt_pmact",``mk_pmact raw_ptpm``);
val _ = overload_on("ptpm",``pmact pt_pmact``);
val _ = overload_on("ptl_pmact",``mk_pmact raw_ptpml``);
val _ = overload_on("ptpml",``pmact ptl_pmact``);

val raw_ptpm_nil = prove(
  ``(∀t:(α,β)pregterm. raw_ptpm [] t = t) ∧
    (∀l:(α,β)pregterm list. raw_ptpml [] l = l)``,
  ho_match_mp_tac oldind >> srw_tac [][raw_ptpm_def])

val raw_ptpm_compose = prove(
  ``(∀t:(α,β)pregterm. raw_ptpm p1 (raw_ptpm p2 t) = raw_ptpm (p1 ++ p2) t) ∧
    (∀l:(α,β)pregterm list.
        raw_ptpml p1 (raw_ptpml p2 l) = raw_ptpml (p1 ++ p2) l)``,
  ho_match_mp_tac oldind >> srw_tac [][raw_ptpm_def, pmact_decompose]);

val raw_ptpm_permeq = prove(
  ``(∀x. lswapstr p1 x = lswapstr p2 x) ⇒
    (∀t:(α,β)pregterm. raw_ptpm p1 t = raw_ptpm p2 t) ∧
    (∀l:(α,β)pregterm list. raw_ptpml p1 l = raw_ptpml p2 l)``,
  strip_tac >> ho_match_mp_tac oldind >> srw_tac [][raw_ptpm_def]);

val ptpm_raw = prove(
  ``(ptpm = raw_ptpm) ∧ (ptpml = raw_ptpml)``,
  conj_tac >> (
  srw_tac [][GSYM pmact_bijections] >>
  srw_tac [][is_pmact_def] >|[
    srw_tac [][raw_ptpm_nil],
    srw_tac [][raw_ptpm_compose],
    fsrw_tac [][raw_ptpm_permeq, permeq_thm, FUN_EQ_THM]
]));
val ptpm_raw = INST_TYPE[gamma|->alpha,delta|->beta] ptpm_raw;

val ptpml_listpm = store_thm(
  "ptpml_listpm",
  ``∀l. ptpml p l = listpm pt_pmact p l``,
  Induct >> fsrw_tac[][ptpm_raw] >>
  srw_tac [][raw_ptpm_def]);

(* |- (!p s vv. ptpm p (var s vv) = var (lswapstr p s) vv) /\
      !p v bv bndts unbndts.
        ptpm p (lam v bv bndts unbndts) =
        lam (lswapstr p v) bv (listpm pt_pmact p bndts)
          (listpm pt_pmact p unbndts)
 *)
Theorem ptpm_thm[simp] =
  raw_ptpm_def |> CONJUNCTS |> (fn l => List.take(l, 2))
               |> map (SUBS (map GSYM (CONJUNCTS ptpm_raw))) |> LIST_CONJ
               |> REWRITE_RULE [ptpml_listpm]

val ptpm_fv = store_thm(
  "ptpm_fv",
  ``(∀t:(α,β)pregterm. fv (ptpm p t) = ssetpm p (fv t)) ∧
    (∀l:(α,β)pregterm list. fvl (ptpml p l) = ssetpm p (fvl l))``,
  ho_match_mp_tac oldind >> srw_tac[][stringpm_raw, ptpml_listpm, pmact_INSERT, pmact_DELETE, pmact_UNION]);
val _ = augment_srw_ss [rewrites [ptpm_fv]]

val allatoms_def = Define`
  (allatoms (var s vv) = {s}) ∧
  (allatoms (lam v bv bndts unbndts) =
     v INSERT allatomsl bndts ∪ allatomsl unbndts) ∧
  (allatomsl [] = ∅) ∧
  (allatomsl (t::ts) = allatoms t ∪ allatomsl ts)
`;

Theorem allatoms_finite[simp] :
    (∀t:(α,β)pregterm. FINITE (allatoms t)) ∧
    (∀l:(α,β)pregterm list. FINITE (allatomsl l))
Proof
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def]
QED

val allatoms_supports = store_thm(
  "allatoms_supports",
  ``(∀t:(α,β)pregterm. support pt_pmact t (allatoms t)) ∧
    (∀l:(α,β)pregterm list. support (list_pmact pt_pmact) l (allatomsl l))``,
  simp_tac (srw_ss())[support_def] >>
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def]);

val allatoms_fresh = store_thm(
  "allatoms_fresh",
  ``x ∉ allatoms t ∧ y ∉ allatoms t ==> (ptpm [(x,y)] t = t)``,
  METIS_TAC [allatoms_supports, support_def]);

val allatoms_apart = store_thm(
  "allatoms_apart",
  ``(∀t:(α,β)pregterm a b.
       a ∉ allatoms t /\ b ∈ allatoms t ⇒ ptpm [(a,b)] t ≠ t) ∧
    (∀l:(α,β)pregterm list a b.
       a ∉ allatomsl l ∧ b ∈ allatomsl l ⇒ listpm pt_pmact [(a,b)] l ≠ l)``,
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def] >>
  metis_tac[swapstr_def]);

val allatoms_supp = store_thm(
  "allatoms_supp",
  ``supp pt_pmact t = allatoms t``,
  MATCH_MP_TAC supp_unique THEN
  SRW_TAC [][allatoms_supports, SUBSET_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [support_def] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `?y. ~(y IN allatoms t) /\ ~(y IN s')`
     by (Q.SPEC_THEN `allatoms t UNION s'` MP_TAC NEW_def THEN
         SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC [allatoms_apart]);

val allatoms_perm = store_thm(
  "allatoms_perm",
  ``(∀t:(α,β)pregterm. allatoms (ptpm p t) = ssetpm p (allatoms t)) ∧
    (∀l:(α,β)pregterm list.
      allatomsl (listpm pt_pmact p l) = ssetpm p (allatomsl l))``,
  ho_match_mp_tac oldind >>
  srw_tac [][allatoms_def, pmact_INSERT, pmact_UNION]);

val (aeq_rules, aeq_ind, aeq_cases) = Hol_reln`
  (!s vv. aeq (var s vv) (var s vv)) /\
  (!u v bv z bndts1 bndts2 us1 us2.
      aeql us1 us2 ∧
      aeql (ptpml [(u,z)] bndts1) (ptpml [(v,z)] bndts2) ∧
      z ∉ allatomsl bndts1 ∧ z ∉ allatomsl bndts2 ∧ z ≠ u ∧ z ≠ v ⇒
      aeq (lam u bv bndts1 us1) (lam v bv bndts2 us2)) ∧
  aeql [] [] ∧
  (∀h1 h2 t1 t2. aeq h1 h2 ∧ aeql t1 t2 ⇒ aeql (h1::t1) (h2::t2))
`;

val aeq_lam = List.nth(CONJUNCTS aeq_rules, 1)

val aeq_distinct = store_thm(
  "aeq_distinct",
  ``~aeq (var s vv) (lam v bv ts us)``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][]);

val aeq_ptpm_lemma = store_thm(
  "aeq_ptpm_lemma",
  ``(!t:(α,β)pregterm u. aeq t u ==> !p. aeq (ptpm p t) (ptpm p u)) ∧
    (∀ts:(α,β)pregterm list us.
      aeql ts us ⇒ ∀π. aeql (listpm pt_pmact π ts) (listpm pt_pmact π us)) ``,
  ho_match_mp_tac aeq_ind >> srw_tac [][aeq_rules, ptpml_listpm] >>
  match_mp_tac aeq_lam >>
  Q.EXISTS_TAC `lswapstr p z` THEN
  srw_tac [][allatoms_perm, pmact_IN] >>
  srw_tac [][ptpml_listpm, pmact_sing_to_back]);

val aeq_ptpm_eqn = store_thm(
  "aeq_ptpm_eqn",
  ``aeq (ptpm p t) u = aeq t (ptpm (REVERSE p) u)``,
  METIS_TAC [aeq_ptpm_lemma, pmact_inverse]);

val aeql_ptpm_eqn = store_thm(
  "aeql_ptpm_eqn",
  ``aeql (ptpml p l1) l2 = aeql l1 (ptpml p⁻¹ l2)``,
  METIS_TAC [aeq_ptpm_lemma, ptpml_listpm, pmact_inverse]);

val IN_fvl = prove(
  ``x ∈ fvl tl ⇔ ∃e. MEM e tl ∧ x ∈ fv e``,
  Induct_on `tl` >> srw_tac [DNF_ss][AC DISJ_ASSOC DISJ_COMM]);

val IN_allatomsl = prove(
  ``x ∈ allatomsl tl ⇔ ∃t. MEM t tl ∧ x ∈ allatoms t``,
  Induct_on `tl` >> srw_tac [DNF_ss][allatoms_def]);

val fv_SUBSET_allatoms = store_thm(
  "fv_SUBSET_allatoms",
  ``(∀t:(α,β)pregterm. fv t SUBSET allatoms t) ∧
    (∀l:(α,β)pregterm list. fvl l ⊆ allatomsl l)``,
  SIMP_TAC (srw_ss()) [SUBSET_DEF] >> ho_match_mp_tac oldind>>
  srw_tac [][allatoms_def] >> metis_tac []);

val aeq_fv = store_thm(
  "aeq_fv",
  ``(!t:(α,β)pregterm u. aeq t u ==> (fv t = fv u)) ∧
    (∀ts:(α,β)pregterm list us. aeql ts us ⇒ (fvl ts = fvl us))``,
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
  ]);

Theorem aeq_refl[simp] :
    (∀t:(α,β)pregterm. aeq t t) ∧ (∀l:(α,β)pregterm list. aeql l l)
Proof
  ho_match_mp_tac oldind >> asm_simp_tac (srw_ss())[aeq_rules] >>
  REPEAT gen_tac >> strip_tac >>
  MAP_EVERY Q.X_GEN_TAC [`b`, `s`] >>
  MATCH_MP_TAC aeq_lam >>
  SRW_TAC [][aeql_ptpm_eqn, ptpml_listpm] THEN
  Q.SPEC_THEN `s INSERT allatomsl l` MP_TAC NEW_def THEN SRW_TAC [][] THEN
  METIS_TAC [pmact_sing_inv]
QED

val aeq_sym = store_thm(
  "aeq_sym",
  ``(∀t:(α,β)pregterm u. aeq t u ==> aeq u t) ∧
    (∀l1:(α,β)pregterm list l2. aeql l1 l2 ==> aeql l2 l1)``,
  ho_match_mp_tac aeq_ind >> srw_tac [][aeq_rules] >>
  metis_tac [aeq_lam]);

val aeq_var_inversion = store_thm(
  "aeq_var_inversion",
  ``aeq (var vv s) t = (t = var vv s)``,
  srw_tac [][Once aeq_cases]);

val aeq_lam_inversion = store_thm(
  "aeq_lam_inversion",
  ``aeq (lam v bv bndts unbndts) N =
      ∃z v' bndts' unbndts'.
        (N = lam v' bv bndts' unbndts') ∧ z ≠ v' ∧ z ≠ v ∧
        z ∉ allatomsl bndts ∧ z ∉ allatomsl bndts' ∧
        aeql (ptpml [(v,z)] bndts) (ptpml [(v',z)] bndts') ∧
        aeql unbndts unbndts'``,
  srw_tac [][Once aeq_cases, SimpLHS] >> metis_tac []);

Theorem aeq_ptm_11:
    (aeq (var s1 vv1) (var s2 vv2) ⇔ (s1 = s2) ∧ (vv1 = vv2)) /\
    (aeq (lam v bv1 bndts1 unbndts1) (lam v bv2 bndts2 unbndts2) ⇔
      (bv1 = bv2) ∧ aeql bndts1 bndts2 ∧ aeql unbndts1 unbndts2)
Proof
  SRW_TAC [][aeq_lam_inversion, aeq_ptpm_eqn, aeq_var_inversion, EQ_IMP_THM]
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

val ptpml_sing_to_back' = prove(
  ``ptpml p (ptpml [(u,v)] tl) =
       ptpml [(lswapstr p u, lswapstr p v)] (ptpml p tl)``,
  simp_tac (srw_ss()) [pmact_sing_to_back]);

(* proof follows that on p169 of Andy Pitts, Information and Computation 186
   article: Nominal logic, a first order theory of names and binding *)
val aeq_trans = store_thm(
  "aeq_trans",
  ``(∀t:(α,β)pregterm u. aeq t u ⇒ ∀v. aeq u v ==> aeq t v) ∧
    (∀l1:(α,β)pregterm list l2. aeql l1 l2 ⇒ ∀l3. aeql l2 l3 ⇒ aeql l1 l3)``,
  ho_match_mp_tac aeq_ind >> REPEAT conj_tac >|[
    srw_tac [][],
    Q_TAC SUFF_TAC
      `∀u v bv z bt1 bt2 ut1 (ut2:(α,β)pregterm list).
         (∀l3. aeql (ptpml [(v,z)] bt2) l3 ⇒ aeql (ptpml [(u,z)] bt1) l3) ∧
         (∀ut3. aeql ut2 ut3 ⇒ aeql ut1 ut3) ∧
         z ∉ allatomsl bt1 ∧ z ∉ allatomsl bt2 ∧ z ≠ u ∧ z ≠ v ⇒
         ∀t3. aeq (lam v bv bt2 ut2) t3 ⇒ aeq (lam u bv bt1 ut1) t3`
          >- metis_tac [] >>
    rpt gen_tac >> strip_tac >> gen_tac >>
    simp_tac (srw_ss()) [SimpL ``$==>``, aeq_lam_inversion] >>
    DISCH_THEN
      (Q.X_CHOOSE_THEN `z2`
         (Q.X_CHOOSE_THEN `w`
              (Q.X_CHOOSE_THEN `bt3`
                  (Q.X_CHOOSE_THEN `ut3` STRIP_ASSUME_TAC)))) >>
    Q_TAC (NEW_TAC "d")
       `{z;z2;u;v;w} ∪ allatomsl bt1 ∪ allatomsl bt2 ∪ allatomsl bt3` >>
    `∀bt3.
       aeql (ptpml [(z,d)] (ptpml [(v,z)] bt2)) (ptpml [(z,d)] bt3) ==>
       aeql (ptpml [(z,d)] (ptpml [(u,z)] bt1)) (ptpml [(z,d)] bt3)`
       by FULL_SIMP_TAC (srw_ss()) [aeql_ptpm_eqn] THEN
    POP_ASSUM
       (Q.SPEC_THEN `ptpml [(z,d)] bt3`
           (ASSUME_TAC o Q.GEN `bt3` o
            SIMP_RULE (srw_ss() ++ ETA_ss)
                      [pmact_sing_inv, pmact_nil])) THEN
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ptpml_sing_to_back']) THEN
    SRW_TAC [][swapstr_def, ptpml_fresh] THEN
    `aeql (ptpml [(z2,d)] (ptpml [(v,z2)] bt2))
          (ptpml [(z2,d)] (ptpml [(w,z2)] bt3))`
       by (srw_tac [ETA_ss]
                   [Once aeql_ptpm_eqn, pmact_nil]) >>
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ptpml_sing_to_back']) THEN
    SRW_TAC [][swapstr_def, ptpml_fresh] THEN
    `aeql (ptpml [(u,d)] bt1) (ptpml [(w,d)] bt3)` by METIS_TAC [] THEN
    METIS_TAC [aeq_lam],

    srw_tac [][],
    rpt gen_tac >> strip_tac >> gen_tac >>
    srw_tac [][Once aeq_cases, SimpL ``$==>``] >>
    metis_tac [aeq_rules]
  ]);

val aeq_equiv = store_thm(
  "aeq_equiv",
  ``!t1 t2. aeq t1 t2 = (aeq t1 = aeq t2)``,
  srw_tac [][FUN_EQ_THM] >> METIS_TAC [aeq_trans, aeq_sym, aeq_refl]);

val alt_aeq_lam = store_thm(
  "alt_aeq_lam",
  ``(∀z. z ∉ allatomsl t1 ∧ z ∉ allatomsl t2 ∧ z ≠ u ∧ z ≠ v ⇒
         aeql (ptpml [(u,z)] t1) (ptpml [(v,z)] t2)) ∧
    aeql u1 u2 ⇒
    aeq (lam u bv t1 u1) (lam v bv t2 u2)``,
  strip_tac >> MATCH_MP_TAC aeq_lam >>
  Q_TAC (NEW_TAC "z")
     `allatomsl t1 ∪ allatomsl t2 ∪ {u;v}` >>
  METIS_TAC []);

val fresh_swap = store_thm(
  "fresh_swap",
  ``(∀t:(α,β)pregterm x y. x ∉ fv t ∧ y ∉ fv t ⇒ aeq t (ptpm [(x, y)] t)) ∧
    (∀l:(α,β)pregterm list x y.
       x ∉ fvl l ∧ y ∉ fvl l ⇒ aeql l (ptpml [(x,y)] l))``,
  ho_match_mp_tac oldind >>
  asm_simp_tac (srw_ss()) [aeq_rules,ptpml_listpm] >>
  map_every qx_gen_tac [`bt`, `ut`] >> strip_tac >>
  map_every qx_gen_tac [`b`, `s`,`x`,`y`] >>
  strip_tac >> srw_tac [][] >>
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
  ]);

Theorem lam_aeq_thm:
    aeq (lam v1 bv1 t1 u1) (lam v2 bv2 t2 u2) ⇔
       (v1 = v2) ∧ (bv1 = bv2) ∧ aeql t1 t2 ∧ aeql u1 u2 ∨
       v1 ≠ v2 ∧ (bv1 = bv2) ∧ v1 ∉ fvl t2 ∧ aeql t1 (ptpml [(v1,v2)] t2) ∧
       aeql u1 u2
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
  ``!v bv t1 t2 u1 u2.
      aeql t1 t2 ∧ aeql u1 u2 ==> aeq (lam v bv t1 u1) (lam v bv t2 u2)``,
  srw_tac [][] >> match_mp_tac aeq_lam >>
  srw_tac [][aeql_ptpm_eqn, pmact_sing_inv] >>
  Q_TAC (NEW_TAC "z") `v INSERT allatomsl t1 ∪ allatomsl t2` >> metis_tac []);

val rmaeql = REWRITE_RULE [aeql_LIST_REL]

val var_respects_aeq = store_thm(
  "var_respects_aeq",
  ``!s1 s2 vv1 vv2. (s1 = s2) ∧ (vv1 = vv2) ==> aeq (var s1 vv1) (var s2 vv2)``,
  SRW_TAC [][]);

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

val fvl_eqrespects = prove(
  ``∀ts1 ts2:(α,β) pregterm list. (ts1 = ts2) ==> (fvl ts1 = fvl ts2)``,
  srw_tac [][]);

val pregterm_size_def = definition "pregterm_size_def";

Definition psize_def:
  (psize (var s vv) = 1) ∧
  (psize (lam s bv ts us) = SUM (MAP psize ts) + SUM (MAP psize us) + 1)
Termination
 WF_REL_TAC `measure (pregterm_size (K 0) (K 0))` >>
 conj_tac >> (ntac 3 gen_tac) >> Induct >>
 srw_tac [ARITH_ss][pregterm_size_def] >>
 fsrw_tac [][] >> res_tac >> DECIDE_TAC
End

val psize_thm = SIMP_RULE (srw_ss()++ETA_ss) [] psize_def

val psize_ptpm0 = prove(
``(∀p:(α,β)pregterm pi. psize (ptpm pi p) = psize p) /\
  (∀pl:(α,β)pregterm list pi. MAP psize (ptpml pi pl) = MAP psize pl)``,
ho_match_mp_tac oldind >>
srw_tac [][psize_thm, ptpml_listpm]);

val psize_raw_ptpm = psize_ptpm0 |> CONJUNCT1 |> REWRITE_RULE [ptpm_raw]

val psize_respects = prove(
  ``∀t1 t2. aeq t1 t2 ⇒ (psize t1 = psize t2)``,
qsuff_tac `(∀(t1:('a,'b) pregterm) t2. aeq t1 t2 ⇒ (psize t1 = psize t2)) ∧
           (∀(l1:('a,'b) pregterm list) l2. aeql l1 l2 ⇒ (SUM (MAP psize l1) = SUM (MAP psize l2)))`
  >- metis_tac [] >>
ho_match_mp_tac aeq_ind >>
srw_tac [][psize_thm] >>
fsrw_tac [][psize_ptpm0]);

val [GFV_thm0, gfvl_thm, GFV_raw_gtpm, simple_induction0,
     raw_gtpm_thm, is_pmact_raw_gtpm,
     gterm_distinct, gterm_11,
     GLAM_eq_thm0, FRESH_swap0,
     FINITE_GFV, gtmsize_thm, gtmsize_raw_gtpm] =
    quotient.define_quotient_types_full
    {
     types = [{name = "gterm", equiv = aeq_equiv}],
     defs = map mk_def
       [("GLAM", ``lam:string -> α -> (α,β)pregterm list ->
                       (α,β)pregterm list -> (α,β)pregterm``),
        ("GVAR", ``var:string -> β -> (α,β)pregterm``),
        ("GFV", ``fv : (α,β)pregterm -> string set``),
        ("gfvl", ``fvl : (α,β)pregterm list -> string set``),
        ("raw_gtpm", ``raw_ptpm : pm -> (α,β)pregterm -> (α,β)pregterm``),
        ("gtmsize", ``psize:(α,β)pregterm ->num``)],
     tyop_equivs = [],
     tyop_quotients = [],
     tyop_simps = [],
     respects = [rmaeql lam_respects_aeq,
                 var_respects_aeq, CONJUNCT1 aeq_fv,
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
     old_thms = [fv_def |> CONJUNCTS |> front 2 |> LIST_CONJ,
                 fv_def |> CONJUNCTS |> drop 2 |> LIST_CONJ,
                 ptpm_fv', pind,
                 ptpm_thm |> CONJUNCTS |> front 2 |> LIST_CONJ |> rmptpml,
                 is_pmact_pmact |> Q.ISPEC `pt_pmact` |> REWRITE_RULE [ptpm_raw,is_pmact_def],
                 aeq_distinct, rmaeql aeq_ptm_11,
                 rmptpml (rmaeql lam_aeq_thm),
                 CONJUNCT1 fresh_swap |> REWRITE_RULE [ptpm_raw],
                 finite_fv,
                 psize_thm, psize_raw_ptpm]}

val simple_induction = save_thm(
  "simple_induction",
  REWRITE_RULE [EVERY_MEM] simple_induction0)

val _ = overload_on("gt_pmact",``mk_pmact raw_gtpm``);
val _ = overload_on("gtpm",``pmact gt_pmact``);

val gtpm_raw = store_thm(
  "gtpm_raw",
  ``gtpm = raw_gtpm``,
  srw_tac [][GSYM pmact_bijections,is_pmact_def,is_pmact_raw_gtpm]);

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
  srw_tac [][] >> metis_tac[swapstr_def]);

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

val gtmsize_gtpm = CONJ (SUBS [GSYM gtpm_raw] gtmsize_raw_gtpm) (GEN_ALL gtmsize_gtpml)

(* don't export any of these, because the intention is not to have users
   working with this type *)
val GFV_thm = save_thm("GFV_thm", rmGFV GFV_thm0)
val GFV_gtpm = save_thm("GFV_gtpm", rmGFV (SUBS [GSYM gtpm_raw] GFV_raw_gtpm))
Theorem gtpm_thm[allow_rebind] = REWRITE_RULE [MAP_gtpm] gtpm_thm
val gterm_distinct = save_thm("gterm_distinct", gterm_distinct)
val gterm_11 = save_thm("gterm_11", gterm_11)
val GLAM_eq_thm = save_thm("GLAM_eq_thm", rmGFV GLAM_eq_thm1)
val gtpm_fresh = save_thm("gtpm_fresh", rmGFV (SUBS [GSYM gtpm_raw] (GSYM FRESH_swap0)))
val FINITE_GFV = save_thm("FINITE_GFV", rmGFV FINITE_GFV)
val IN_GFVl = save_thm("IN_GFVl", rmGFV IN_gfvl)

val _ = delete_const "gfvl"
val _ = delete_const "GFV"
val _ = delete_const "fv"

val _ = overload_on ("GFV", ``supp gt_pmact``)
val _ = overload_on ("GFVl", ``supp (list_pmact gt_pmact)``)

val _ = augment_srw_ss [rewrites [gterm_distinct]]


(* default rewriting of negations makes a mess of these. *)
val NOT_IN_GFV = store_thm(
  "NOT_IN_GFV",
  ``(x ∉ GFV (GVAR s vv) ⇔ x ≠ s) ∧
    (x ∉ GFV (GLAM v bv ts us) ⇔
       (∀u. MEM u us ⇒ x ∉ GFV u) ∧
       (∀t. x ≠ v ∧ MEM t ts ⇒ x ∉ GFV t))``,
  srw_tac [][GFV_thm, IN_GFVl] >> metis_tac []);

val GLAM_NIL_EQ = store_thm(
  "GLAM_NIL_EQ",
  ``(GLAM u bv1 [] ts = GLAM v bv2 [] ts') ⇔ (bv1 = bv2) ∧ (ts = ts')``,
  srw_tac [][GLAM_eq_thm] >> metis_tac []);

val list_rel_split = prove(
  ``LIST_REL (λx y. P x y ∧ Q x y) l1 l2 ⇔
      LIST_REL P l1 l2 ∧ LIST_REL Q l1 l2``,
  qid_spec_tac `l2` >> Induct_on `l1` >> Cases_on `l2` >> srw_tac [][] >>
  metis_tac []);

(* generic sub-type of a generic term, where one is only allowed to look
   at the data attached to the GLAM and the number of arguments in the lists *)
val (genind_rules, genind_ind, genind_cases) = Hol_reln`
  (∀n:num s vv. vp n vv ==> genind vp lp n (GVAR s vv)) ∧
  (∀n v bv ts us tns uns.
     LIST_REL (genind vp lp) tns ts ∧
     LIST_REL (genind vp lp) uns us ∧
     lp n bv tns uns  ⇒
     genind vp lp n (GLAM v bv ts us))
`;

val grules' = genind_rules |> SPEC_ALL |> CONJUNCTS

val genind_gtpm = store_thm(
  "genind_gtpm",
  ``∀n t. genind vp lp n t ⇒ ∀pi. genind vp lp n (gtpm pi t)``,
  Induct_on `genind` >>
  srw_tac [DNF_ss][gtpm_thm, genind_rules, list_rel_split] >>
  match_mp_tac (List.nth(grules', 1)) >>
  fsrw_tac [CONJ_ss][LIST_REL_EL_EQN,EL_MAP] >>
  srw_tac [][] >> metis_tac [])

val genind_gtpm_eqn = store_thm(
  "genind_gtpm_eqn",
  ``genind vp lp n (gtpm pi t) = genind vp lp n t``,
  metis_tac [pmact_inverse, genind_gtpm]);
val _ = augment_srw_ss [rewrites [genind_gtpm_eqn]]

val LIST_REL_genind_gtpm_eqn = store_thm(
  "LIST_REL_genind_gtpm_eqn",
  ``LIST_REL (genind vp lp) ns (listpm gt_pmact pi ts) =
    LIST_REL (genind vp lp) ns ts``,
  qid_spec_tac `ns` >> Induct_on `ts` >> Cases_on `ns` >>
  fsrw_tac [][]);

val _ = augment_srw_ss [rewrites [FINITE_GFV, LIST_REL_genind_gtpm_eqn]]

val _ = overload_on ("gtpml", ``listpm gt_pmact``)

val gtpml_eqr = store_thm(
"gtpml_eqr",
``!t u. (t = gtpml pi u) = (gtpml (REVERSE pi) t = u)``,
srw_tac [][pmact_eql]);

val genind_GLAM_eqn = store_thm(
  "genind_GLAM_eqn",
  ``genind vp lp n (GLAM v bv ts us) =
      ∃tns uns. LIST_REL (genind vp lp) tns ts ∧
                LIST_REL (genind vp lp) uns us ∧
                lp n bv tns uns``,
  srw_tac [DNF_ss][genind_cases, gterm_distinct, GLAM_eq_thm] >>
  srw_tac [][gtpml_eqr, perm_supp] >> metis_tac []);

val finite_gfvl = prove(
  ``FINITE (GFVl ts)``,
  Induct_on `ts` >> srw_tac [][MEM_MAP] >> srw_tac [][]);

val _ = augment_srw_ss [rewrites [finite_gfvl]]

val bvc_genind = store_thm(
  "bvc_genind",
  ``∀P fv.
      (∀x. FINITE (fv x)) ∧
      (∀n s vv x. vp n vv ⇒ P n (GVAR s vv) x) ∧
      (∀n v bv tns uns ts us x.
         LIST_REL (λn t. genind vp lp n t ∧ ∀x. P n t x) tns ts ∧
         LIST_REL (λn t. genind vp lp n t ∧ ∀x. P n t x) uns us ∧
         lp n bv tns uns ∧ v ∉ fv x ∧ v ∉ supp (list_pmact gt_pmact) us
        ⇒
         P n (GLAM v bv ts us) x)
   ⇒
      ∀n t. genind vp lp n t ⇒ ∀x. P n t x``,
  rpt GEN_TAC >> strip_tac >>
  qsuff_tac `∀n t. genind vp lp n t ⇒ ∀pi x. P n (gtpm pi t) x`
  >- metis_tac [pmact_nil] >>
  Induct_on `genind` >> srw_tac [DNF_ss][gtpm_thm, list_rel_split] >>
  Q_TAC (NEW_TAC "z")
    `fv x ∪ {lswapstr pi v; v} ∪ GFVl (gtpml pi us) ∪ GFVl (gtpml pi ts)` >>
  `GLAM (lswapstr pi v) bv (gtpml pi ts) (gtpml pi us) =
   GLAM z bv (gtpml [(z,lswapstr pi v)] (gtpml pi ts)) (gtpml pi us)`
     by (srw_tac [][GLAM_eq_thm, NOT_IN_supp_listpm]
         >- fsrw_tac [DNF_ss][MEM_listpm_EXISTS, NOT_IN_supp_listpm,
                              GFV_gtpm] >>
         srw_tac [ETA_ss][pmact_flip_args, pmact_nil]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum match_mp_tac >>
  map_every qexists_tac [`tns`, `uns`] >>
  asm_simp_tac (srw_ss() ++ DNF_ss) [] >>
  fsrw_tac [CONJ_ss][LIST_REL_EL_EQN, EL_listpm] >>
  srw_tac [][GSYM pmact_decompose])

val genindX =
    bvc_genind |> Q.SPEC `λn t x. Q n t`
               |> Q.SPEC `λx. X`
               |> SIMP_RULE (srw_ss()) []
               |> Q.INST [`Q` |-> `P`] |> GEN_ALL

val genind_KT = prove(
  ``∀n t. genind (λn vv. T) (λn bv tns uns. T) n t``,
  CONV_TAC SWAP_FORALL_CONV >> ho_match_mp_tac simple_induction >>
  srw_tac [][]
  >- (match_mp_tac (hd grules') >> srw_tac [][]) >>
  match_mp_tac (hd (tl grules')) >>
  map_every qexists_tac [`GENLIST (K 0) (LENGTH bndts)`,
                         `GENLIST (K 0) (LENGTH unbndts)`] >>
  fsrw_tac[DNF_ss] [LIST_REL_EL_EQN, MEM_EL]);

val vacuous_list_rel = prove(
  ``LIST_REL (λx y. P y) xs ys ⇔
     (∀y. MEM y ys ⇒ P y) ∧ (LENGTH xs = LENGTH ys)``,
  qid_spec_tac `ys` >> Induct_on `xs` >> Cases_on `ys` >> srw_tac [][] >>
  metis_tac []);

val silly = prove(
  ``(∀v bv tns uns ts us x.
       LIST_REL (λn:num t. ∀x. Q t x) tns ts ∧
       LIST_REL (λn:num t. ∀x. Q t x) uns us ∧ v ∉ fv x ∧
       v ∉ supp (list_pmact gt_pmact) us ⇒
       Q (GLAM v bv ts us) x) ⇔
   (∀v bv ts us x.
      (∀t x. MEM t ts ⇒ Q t x) ∧ (∀u x. MEM u us ⇒ Q u x) ∧
      v ∉ fv x ∧ v ∉ supp (list_pmact gt_pmact) us ⇒
      Q (GLAM v bv ts us) x)``,
  srw_tac [][EQ_IMP_THM, vacuous_list_rel] >>
  first_x_assum (Q.SPECL_THEN [`v`,`bv`,`GENLIST (K 0) (LENGTH ts)`,
                               `GENLIST (K 0) (LENGTH us)`] MP_TAC) >>
  srw_tac [][]);

val gen_bvc_induction =
    bvc_genind |> SPEC_ALL
               |> Q.INST [`lp` |-> `(λn bv tns uns. T)`,
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

val gterm_cases = store_thm(
"gterm_cases",
``∀t. (∃s vv. t = GVAR s vv) ∨ (∃s bv ts us. t = GLAM s bv ts us)``,
ho_match_mp_tac simple_induction >>
srw_tac [][] >> metis_tac []);

Theorem FORALL_gterm:
  (∀t. P t) ⇔ (∀s v. P (GVAR s v)) ∧ (∀s bv ts us. P (GLAM s bv ts us))
Proof
  EQ_TAC >> srw_tac [][] >>
  qspec_then `t` STRUCT_CASES_TAC gterm_cases >> srw_tac [][]
QED

val some_4_F = prove(
  ``(some (w,x,y,z). F) = NONE``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

val SUM_MAP_MEM = Q.store_thm(
"SUM_MAP_MEM",
`∀f x l. MEM x l ⇒ f x ≤ SUM (MAP f l)`,
ntac 2 gen_tac >> Induct >> srw_tac [][] >>
fsrw_tac [ARITH_ss][]);

val vf = mk_var ("vf", ``: string -> β -> ρ -> γ``)
val lf = mk_var ("lf", ``: string -> α -> (ρ -> γ) list -> (ρ -> γ) list
                           -> (α,β)gterm list -> (α,β)gterm list -> ρ -> γ``)

val trec = ``tmrec (A: string set) (ppm: ρ pmact) ^vf ^lf : (α,β)gterm -> ρ -> γ``

val tmrec_defn = Hol_defn "tmrec" `
  ^trec t = λp.
    case some(s,vv).(t = GVAR s vv) of
      SOME (s,vv) => vf s vv p
    | NONE => (
    case some(v,bv,ts,us).(t = GLAM v bv ts us) ∧ v ∉ supp ppm p ∧ v ∉ GFVl us ∧ v ∉ A of
      SOME (v,bv,ts,us) => lf v bv (MAP (^trec) ts) (MAP (^trec) us) ts us p
    | NONE => ARB)`

val (tmrec_def, tmrec_ind) = Defn.tprove(
  tmrec_defn,
  WF_REL_TAC `measure (gtmsize o SND o SND o SND o SND)` >>
  srw_tac [][] >>
  qspec_then `t` FULL_STRUCT_CASES_TAC gterm_cases >>
  fsrw_tac [][some_4_F,gterm_distinct] >>
  fsrw_tac [][GLAM_eq_thm] >>
  qpat_x_assum `X = SOME Y` mp_tac >>
  DEEP_INTRO_TAC optionTheory.some_intro >>
  simp_tac (srw_ss()) [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] >>
  srw_tac [][gtmsize_thm] >>
  Q.ISPEC_THEN `gtmsize` imp_res_tac SUM_MAP_MEM >>
  srw_tac [][gtmsize_gtpm] >>
  DECIDE_TAC)

val vp = ``vp: num -> β -> bool``
val lp = ``lp: num -> α -> num list -> num list -> bool``

val _ = temp_overload_on ("→", ``fnpm``)
val _ = temp_set_fixity "→" (Infixr 700)

val relsupp_def = Define`
  relsupp A dpm ppm t r <=>
    ∀x. x ∉ A ∧ x ∉ GFV t ==> x ∉ supp (fn_pmact ppm dpm) r
`;

val sidecond_def = Define`
  sidecond dpm ppm A ^vp ^lp ^vf ^lf ⇔
  FINITE A ∧ (∀p. FINITE (supp ppm p)) ∧
    (∀x y s vv n p.
       x ∉ A ∧ y ∉ A ∧ genind vp lp n (GVAR s vv) ⇒
       (pmact dpm [(x,y)] (^vf s vv p) =
        ^vf (lswapstr [(x,y)] s) vv (pmact ppm [(x,y)] p))) ∧
    (∀x y n v bv r1 r2 ts us p.
       x ∉ A ∧ y ∉ A ∧ v ∉ A ∧
       genind vp lp n (GLAM v bv ts us) ∧
       LIST_REL (relsupp A dpm ppm) ts r1 ∧
       LIST_REL (relsupp A dpm ppm) us r2 ∧
       v ∉ supp ppm p ⇒
       (pmact dpm [(x,y)] (^lf v bv r1 r2 ts us p) =
        ^lf (lswapstr [(x,y)] v) bv
            (listpm (fn_pmact ppm dpm) [(x,y)] r1)
            (listpm (fn_pmact ppm dpm) [(x,y)] r2)
            (listpm gt_pmact [(x,y)] ts)
            (listpm gt_pmact [(x,y)] us)
            (pmact ppm [(x,y)] p)))`

val FCB_def = Define`
  FCB dpm ppm A ^vp ^lp ^lf ⇔
  ∀a n v bv r1 r2 ts us p.
             a ∉ A ∧ a ∉ GFVl us ∧ a ∉ supp ppm p ∧
             LIST_REL (relsupp A dpm ppm) ts r1 ∧
             LIST_REL (relsupp A dpm ppm) us r2 ∧
             genind vp lp n (GLAM v bv ts us) ⇒
             a ∉ supp dpm (^lf a bv r1 r2 ts us p)`

val some_2_EQ = prove(
  ``(some (x,y). (x' = x) /\ (y' = y)) = SOME(x',y')``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

val some_2_F = prove(
  ``(some (x,y). F) = NONE``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

val tmrec_GVAR = tmrec_def |> Q.INST [`t` |-> `GVAR s vv`]
  |> SIMP_RULE (srw_ss()++ETA_ss) [gterm_11,some_2_EQ]
val tmrec_GLAM = tmrec_def |> Q.INST [`t` |-> `GLAM v bv ts us`]
  |> SIMP_RULE (srw_ss()) [gterm_distinct,some_2_F,NOT_IN_supp_listpm]
  |> C (foldr (uncurry Q.GEN)) [`v`,`bv`,`ts`,`us`]

val gtpm_GVAR = gtpm_thm |> CONJUNCT1
val genind_GVAR = store_thm(
  "genind_GVAR",
  ``genind vp lp n (GVAR s vv) = vp n vv``,
  srw_tac [][genind_cases,gterm_distinct,gterm_11]);
val GFV_GVAR = GFV_thm |> CONJUNCT1

val gtpm_eqr = store_thm(
"gtpm_eqr",
``(t = gtpm pi u) = (gtpm (REVERSE pi) t = u)``,
METIS_TAC [pmact_inverse]);

val lswapstr_sing = Q.prove(`lswapstr [(x,y)] z = swapstr x y z`, srw_tac [][]);

val trec_fnpm = prove(
  ``(ppm → apm) π (tmrec A ppm vf lf t) =
    λp. pmact apm π (tmrec A ppm vf lf t (pmact ppm π⁻¹ p))``,
  srw_tac [][FUN_EQ_THM, fnpm_def]);

val MAP_trec_fnpm = prove(
``MAP ((ppm → dpm) pi o tmrec A ppm vf lf)=
  MAP (λt p. pmact dpm pi (tmrec A ppm vf lf t (pmact ppm (REVERSE pi) p)))``,
ONCE_REWRITE_TAC [FUN_EQ_THM] >>
Induct >> srw_tac [][trec_fnpm]);

val genind_GLAM_subterm = store_thm(
"genind_GLAM_subterm",
``genind vp lp n (GLAM v bv ts us) ∧ (MEM u ts ∨ MEM u us) ⇒
    ∃n. genind vp lp n u``,
srw_tac [][Once genind_cases,gterm_distinct] >>
fsrw_tac [][GLAM_eq_thm] >>
fsrw_tac [][LIST_REL_EL_EQN,MEM_EL] >>
srw_tac [][] >>
fsrw_tac [][EL_MAP] >>
metis_tac []);

val gtmsize_GLAM_subterm = store_thm(
"gtmsize_GLAM_subterm",
``(MEM t ts ∨ MEM t us) ⇒ gtmsize t < gtmsize (GLAM s bv ts us)``,
srw_tac [][gtmsize_thm] >>
imp_res_tac SUM_MAP_MEM >>
pop_assum (qspec_then `gtmsize` mp_tac) >>
DECIDE_TAC);

val LIST_REL_relsupp_gtpml = prove(
  ``∀A dpm ppm l1 l2.
      LIST_REL (relsupp A dpm ppm) l1 l2 ==>
      ∀x y. x ∉ A ∧ y ∉ A ==>
         LIST_REL (relsupp A dpm ppm)
                  (gtpml [(x,y)] l1)
                  (listpm (fn_pmact ppm dpm) [(x,y)] l2)``,
  ntac 3 gen_tac >>
  Induct_on `LIST_REL` >> srw_tac [][relsupp_def, fnpm_def, perm_supp] >>
  first_x_assum match_mp_tac >> srw_tac [][perm_supp] >>
  srw_tac [][swapstr_def])

fun ih_commute_tac dir (asl,w) =
    first_x_assum (fn rwt =>
         if free_in ``gtmsize`` (concl rwt) then
           mp_tac (Q.GEN `n'` (PART_MATCH (lhs o #2 o strip_imp) rwt (dir w)))
         else NO_TAC) (asl,w)

fun sidecond_tac dir =
  qpat_x_assum `sidecond AA BB CC DD EE FF GG`
     (fn th => th |> SIMP_RULE (srw_ss()) [sidecond_def] |> CONJUNCTS
                  |> last |> (fn th' => assume_tac th >> assume_tac th')) >>
  (fn (asl,w) =>
    pop_assum (fn rwt => mp_tac (PART_MATCH (lhs o #2 o strip_imp)
                                            rwt
                                            (dir w))) (asl,w))

val _ = set_trace "Goalstack.print_goal_at_top" 0

val listpm_tMAP = prove(
  ``(listpm apm pi (MAP f l) =
     MAP ((gt_pmact → apm) pi f) (gtpml pi l))``,
  srw_tac [][] >> Induct_on `l` >> srw_tac [][fnpm_def]);

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val tmrec_equivariant = store_thm( (* correct name? *)
"tmrec_equivariant",
``sidecond dpm ppm A ^vp ^lp ^vf ^lf ∧ FCB dpm ppm A ^vp ^lp ^lf ⇒
  ∀n. genind vp lp n t ⇒
      ∀p x y. x ∉ A ∧ y ∉ A ⇒
        (pmact dpm [(x,y)] (tmrec A ppm vf lf t p) =
         tmrec A ppm vf lf (gtpm [(x,y)] t) (pmact ppm [(x,y)] p))``,
strip_tac >>
completeInduct_on `gtmsize t` >>
qabbrev_tac `m = v` >> markerLib.RM_ALL_ABBREVS_TAC >>
pop_assum (strip_assume_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
simp_tac (srw_ss()) [Once FORALL_gterm] >>
conj_tac >- (
  (* GVAR case *)
  srw_tac [][gtpm_GVAR,tmrec_GVAR] >>
  fsrw_tac [][sidecond_def] >>
  metis_tac [lswapstr_sing]) >>
rpt gen_tac >>
disch_then SUBST_ALL_TAC >>
gen_tac >> strip_tac >>
qx_gen_tac `p` >>
Q.SPECL_THEN [`s`,`bv`,`ts`,`us`,`p`] MP_TAC
  (tmrec_GLAM |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]) >>
DEEP_INTRO_TAC optionTheory.some_intro >>
asm_simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
`FINITE A ∧ (∀p. FINITE (supp ppm p))`
   by fsrw_tac [][sidecond_def] >>
reverse conj_tac >- (
  (* bogus some(...) = ARB case *)
  Q_TAC (NEW_TAC "z") `supp ppm p ∪ A ∪ GFVl us ∪ GFVl ts ∪ {s}` >>
  disch_then (qspec_then `z` mp_tac) >>
  asm_simp_tac (srw_ss()++DNF_ss) [GLAM_eq_thm,IN_GFVl,gtpml_eqr,listpm_MAP,MEM_MAP,GFV_gtpm] >>
  fsrw_tac [][IN_GFVl] >>
  metis_tac []) >>
map_every qx_gen_tac [`s'`,`bv'`,`ts'`,`us'`] >>
strip_tac >>
strip_tac >>
`(us' = us) ∧ (bv' = bv)` by fsrw_tac [][GLAM_eq_thm] >> rpt VAR_EQ_TAC >>
asm_simp_tac (srw_ss()++DNF_ss) [gtpm_thm,IN_GFVl,GFV_thm] >>
map_every qx_gen_tac [`x`, `y`] >>
strip_tac >>
qpat_x_assum `tmrec A ppm vf lf (GLAM X Y Z WW) p = XX` (K ALL_TAC) >>
srw_tac [][tmrec_GLAM] >>
DEEP_INTRO_TAC optionTheory.some_intro >>
asm_simp_tac (srw_ss()++ETA_ss) [pairTheory.FORALL_PROD] >>
reverse conj_tac >- (
  (* bogus ARB case *)
  asm_simp_tac (srw_ss()) [GLAM_eq_thm] >>
  Q_TAC (NEW_TAC "z") `{swapstr x y s'} ∪ A ∪ supp ppm (pmact ppm [(x,y)] p) ∪ GFVl (gtpml [(x,y)] us) ∪ GFVl (gtpml [(x,y)] ts')` >>
  disch_then (qspec_then `z` mp_tac) >>
  fsrw_tac [DNF_ss][IN_GFVl,gtpml_eqr,listpm_MAP,MEM_MAP,GFV_gtpm] >>
  reverse conj_tac >- metis_tac [] >>
  conj_tac >- metis_tac [] >>
  srw_tac [][] >> metis_tac []) >>
qabbrev_tac `r1 = MAP (tmrec A ppm vf lf) ts'` >>
qabbrev_tac `r2 = MAP (tmrec A ppm vf lf) us` >>
fsrw_tac [][AND_IMP_INTRO] >>
`∃tns uns. LIST_REL (genind vp lp) tns ts ∧ LIST_REL (genind vp lp) uns us`
  by (fsrw_tac [][genind_cases, GLAM_eq_thm] >> srw_tac [][] >>
      metis_tac []) >>
`LIST_REL (genind vp lp) tns ts'`
   by (fsrw_tac [][GLAM_eq_thm] >> srw_tac [][] >> fsrw_tac [][]) >>
qabbrev_tac `GGSIZE = gtmsize (GLAM s' bv ts' us)` >>
`∀t n' a. gtmsize t < GGSIZE ∧ genind vp lp n' t ∧ a ∉ A ∧ a ∉ GFV t ==>
          a ∉ supp (fn_pmact ppm dpm) (tmrec A ppm vf lf t)`
   by (srw_tac [][] >> match_mp_tac notinsupp_I >>
       qexists_tac `A ∪ GFV t` >>
       srw_tac [][support_def, fnpm_def, FUN_EQ_THM] >>
       metis_tac [supp_fresh, pmact_sing_inv]) >>
`LIST_REL (relsupp A dpm ppm) ts' r1 ∧ LIST_REL (relsupp A dpm ppm) us r2`
  by (srw_tac [][LIST_REL_EL_EQN, relsupp_def, Abbr`r1`, Abbr`r2`] >>
      srw_tac [][EL_MAP] >> first_x_assum match_mp_tac >|
      [qexists_tac `EL n' tns`, qexists_tac `EL n' uns`] >>
      metis_tac [LIST_REL_EL_EQN, MEM_EL, gtmsize_GLAM_subterm]) >>
(* COMPLETE THIS... *)
`∀t p x y.
   (MEM t ts' ∨ MEM t us ∨ MEM t ts) ∧ x ∉ A ∧ y ∉ A ==>
   (pmact dpm [(x,y)] (tmrec A ppm vf lf t p) =
      tmrec A ppm vf lf (gtpm [(x,y)] t) (pmact ppm [(x,y)] p))`
   by (srw_tac [][] >> first_x_assum match_mp_tac >>
       fsrw_tac [][GLAM_eq_thm] >> srw_tac [][] >>
       fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
       metis_tac [genind_GLAM_subterm, gtmsize_GLAM_subterm]) >>
(* THEN COMPLETE THIS ... *)
`(∀a b. a ∉ A ∧ b ∉ A ==>
        (listpm (fn_pmact ppm dpm) [(a,b)] r1 =
         MAP (tmrec A ppm vf lf) (gtpml [(a,b)] ts'))) ∧
 (∀a b. a ∉ A ∧ b ∉ A ==>
        (listpm (fn_pmact ppm dpm) [(a,b)] r2 =
         MAP (tmrec A ppm vf lf) (gtpml [(a,b)] us)))`
  by (asm_simp_tac (srw_ss() ++ DNF_ss)
                   [listpm_tMAP, MAP_EQ_f, MEM_listpm_EXISTS,
                    Abbr`r1`, Abbr`r2`, fnpm_def, FUN_EQ_THM,
                    pmact_sing_inv]) >>
map_every qx_gen_tac [`s''`, `bv'`, `ts''`, `us'`] >>
srw_tac [][] >>
`(bv' = bv) ∧ (us' = gtpml [(x,y)] us)` by fsrw_tac [][GLAM_eq_thm] >>
rpt VAR_EQ_TAC >>
sidecond_tac lhs >>
disch_then (fn th => asm_simp_tac (srw_ss()) [th]) >>
qpat_x_assum `GLAM (swapstr x y s') bv Z1 Z2 = Z3` mp_tac >>
srw_tac [][GLAM_eq_thm] >>
qabbrev_tac `u = swapstr x y s'` >>
fsrw_tac [][gtpml_eqr] >>
qpat_x_assum `XX = ts''` (SUBST_ALL_TAC o SYM) >>
`u ∉ A` by srw_tac [][Abbr`u`,swapstr_def] >>
`u ∉ supp ppm (pmact ppm [(x,y)] p)` by srw_tac [][Abbr`u`,perm_supp] >>
`s'' ∉ supp (list_pmact gt_pmact) (gtpml [(x,y)] us) ∧
 s'' ∉ supp (list_pmact gt_pmact) (gtpml [(x,y)] ts')` by (
  fsrw_tac [DNF_ss][IN_GFVl,listpm_MAP,MEM_MAP,GFV_gtpm] >>
  metis_tac [] ) >>
`u ∉ supp (list_pmact gt_pmact) (gtpml [(x,y)] us)` by (
  fsrw_tac [DNF_ss][IN_GFVl,listpm_MAP,MEM_MAP,GFV_gtpm,Abbr`u`] >>
  metis_tac [] ) >>
`genind vp lp n (GLAM u bv (gtpml [(x,y)] ts') (gtpml [(x,y)] us))` by (
  qmatch_abbrev_tac `genind vp lp n t` >>
  qsuff_tac `t = gtpm [(x,y)] (GLAM s' bv ts' us)` >- srw_tac [][] >>
  srw_tac [][Abbr`t`,gtpm_thm] ) >>
qmatch_abbrev_tac `LHS = RHS` >>
match_mp_tac EQ_TRANS >>
qexists_tac `pmact dpm [(u,s'')] RHS` >>
qabbrev_tac `usxyts = gtpml [(u,s'')] (gtpml [(x,y)] ts')` >>
qabbrev_tac `xyus = gtpml [(x,y)] us` >>
`genind vp lp n (GLAM s'' bv usxyts xyus)`
  by(first_x_assum (mp_tac o MATCH_MP genind_gtpm) >>
     disch_then (qspec_then `[(u,s'')]` mp_tac) >>
     CONV_TAC (LAND_CONV (RAND_CONV (REWRITE_CONV [gtpm_thm]))) >>
     asm_simp_tac (srw_ss()) [supp_fresh]) >>
`LIST_REL (relsupp A dpm ppm) usxyts (MAP (tmrec A ppm vf lf) usxyts) ∧
 LIST_REL (relsupp A dpm ppm) xyus (MAP (tmrec A ppm vf lf) xyus)`
   by (map_every qunabbrev_tac [`r1`, `r2`, `usxyts`, `xyus`] >>
       rpt (first_x_assum (mp_tac o MATCH_MP LIST_REL_relsupp_gtpml)) >>
       rpt (disch_then (qspecl_then [`x`,`y`] assume_tac)) >>
       ntac 2 (pop_assum mp_tac) >> asm_simp_tac (srw_ss()) [] >>
       rpt (disch_then (assume_tac o MATCH_MP LIST_REL_relsupp_gtpml)) >>
       ntac 2 (pop_assum (qspecl_then [`u`, `s''`] mp_tac)) >>
       asm_simp_tac (srw_ss()) [listpm_tMAP] >>
       rpt (disch_then assume_tac) >>
       qpat_x_assum `LIST_REL _ (_ (_ ts')) (MAP _ _)` mp_tac >>
       qmatch_abbrev_tac
        `LIST_REL RR TS (MAP f1 TS) ==> LIST_REL RR TS (MAP f2 TS)` >>
       qsuff_tac `MAP f1 TS = MAP f2 TS` >- srw_tac [][] >>
       srw_tac [][MAP_EQ_f] >>
       map_every qunabbrev_tac [`f1`, `f2`, `TS`] >>
       asm_simp_tac (srw_ss()) [FUN_EQ_THM, fnpm_def] >> gen_tac >>
       ih_commute_tac lhs >> asm_simp_tac (srw_ss()) [pmact_sing_inv] >>
       disch_then match_mp_tac >>
       fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
       metis_tac [gtmsize_GLAM_subterm, genind_GLAM_subterm]) >>
reverse conj_tac >- (
  match_mp_tac supp_fresh >>
  reverse conj_tac >- (
    fsrw_tac [][FCB_def,Abbr`RHS`] >>
    first_x_assum match_mp_tac >>
    asm_simp_tac (srw_ss()) [] >>
    map_every qexists_tac [`n`,`s''`] >>
    srw_tac [][]) >>
  match_mp_tac notinsupp_I >>
  qunabbrev_tac `RHS` >>
  qexists_tac
     `A ∪ {s''} ∪ supp ppm (pmact ppm [(x,y)] p) ∪ GFVl xyus ∪ GFVl usxyts` >>
  `FINITE A ∧ (∀p. FINITE (supp ppm p))` by fsrw_tac [][sidecond_def] >>
  asm_simp_tac (srw_ss()) [support_def] >>
  map_every qx_gen_tac [`w`,`z`] >>
  strip_tac >>
  sidecond_tac lhs >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (K ALL_TAC) >>
  asm_simp_tac (srw_ss()) [listpm_tMAP, supp_fresh] >>
  rpt AP_THM_TAC >>
  qmatch_abbrev_tac `lf s'' bv X1 Y1 = lf s'' bv X2 Y2` >>
  qsuff_tac `(X1 = X2) ∧ (Y1 = Y2)` >- srw_tac [][] >>
  map_every qunabbrev_tac [`X1`, `X2`, `Y1`, `Y2`] >>
  asm_simp_tac (srw_ss() ++ DNF_ss)
               [MAP_EQ_f, MEM_listpm_EXISTS, FUN_EQ_THM, fnpm_def] >>
  srw_tac [][] >> (* two similar goals here-on *)
  ih_commute_tac lhs >>
  asm_simp_tac (srw_ss()) [gtmsize_gtpm, pmact_sing_inv] >>
  disch_then match_mp_tac >>
  map_every qunabbrev_tac [`usxyts`, `xyus`] >>
  fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
  metis_tac [gtmsize_GLAM_subterm, genind_GLAM_subterm]) >>
srw_tac [][Abbr`RHS`] >>
sidecond_tac rhs >>
asm_simp_tac (srw_ss()) [listpm_tMAP, supp_fresh] >>
disch_then (K ALL_TAC) >>
qunabbrev_tac `LHS` >> rpt AP_THM_TAC >>
qunabbrev_tac `usxyts` >>
asm_simp_tac (srw_ss() ++ ETA_ss) [pmact_sing_inv, pmact_nil] >>
AP_THM_TAC >>
qmatch_abbrev_tac `lf u bv X1 Y1 = lf u bv X2 Y2` >>
qsuff_tac `(X1 = X2) ∧ (Y1 = Y2)` >- srw_tac [][] >>
map_every qunabbrev_tac [`X1`,`X2`,`Y1`, `Y2`] >>
conj_tac >> (* splits in two *)
srw_tac [][MAP_EQ_f, FUN_EQ_THM, fnpm_def] >>
ih_commute_tac rhs >>
asm_simp_tac (srw_ss()) [pmact_sing_inv, gtmsize_gtpm] >>
disch_then (match_mp_tac o GSYM) >>
qunabbrev_tac `xyus` >>
fsrw_tac [][MEM_listpm_EXISTS, gtmsize_gtpm] >>
metis_tac [genind_GLAM_subterm, gtmsize_GLAM_subterm]);

fun udplus th =
    th |> REWRITE_RULE [GSYM CONJ_ASSOC]
       |> repeat (UNDISCH o CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)))
       |> UNDISCH

val eqv_I = tmrec_equivariant |> udplus

val tmrec_fresh = store_thm(
  "tmrec_fresh",
  ``sidecond dpm ppm A ^vp ^lp ^vf ^lf ∧ FCB dpm ppm A vp lp lf ==>
    ∀n t. genind vp lp n t ==>
          ∀x. x ∉ A ∧ x ∉ GFV t ==>
              x ∉ supp (fn_pmact ppm dpm) (tmrec A ppm vf lf t)``,
  srw_tac [][] >> match_mp_tac notinsupp_I >> qexists_tac `GFV t ∪ A` >>
  `FINITE A` by fsrw_tac [][sidecond_def] >>
  srw_tac [][support_def, FUN_EQ_THM, fnpm_def] >>
  metis_tac [tmrec_equivariant, supp_fresh, pmact_sing_inv]);

val NEWFCB_def = Define`
  NEWFCB dpm ppm A vp lp lf ⇔
  ∀a1 a2 n bv r1 r2 ts us p.
     a1 ∉ A ∧ a1 ∉ supp ppm p ∧ a2 ∉ A ∧ a2 ∉ GFVl ts ∧ a2 ∉ supp ppm p ∧
     LIST_REL (relsupp A dpm ppm) ts r1 ∧
     LIST_REL (relsupp A dpm ppm) us r2 ∧
     genind vp lp n (GLAM a1 bv ts us) ==>
     (lf a2 bv (listpm (fn_pmact ppm dpm) [(a2,a1)] r1) r2
               (gtpml [(a2,a1)] ts) us p =
      lf a1 bv r1 r2 ts us p)
`

val LIST_REL_combined_supps = prove(
  ``LIST_REL (relsupp A dpm ppm) ts rs ∧ x ∉ A ∧ x ∉ GFVl ts ==>
    x ∉ supp (list_pmact (fn_pmact ppm dpm)) rs``,
  qsuff_tac
    `∀ts rs. LIST_REL (relsupp A dpm ppm) ts rs ==>
             ∀x. x ∉ GFVl ts ∧ x ∉ A ==> x ∉ supp (list_pmact (fn_pmact ppm dpm)) rs`
    >- metis_tac [] >>
  Induct_on `LIST_REL` >> srw_tac [][relsupp_def]);

val NEWFCB_OLD = prove(
  ``NEWFCB dpm ppm A vp lp ^lf ∧ sidecond dpm ppm A vp lp vf lf ==>
    FCB dpm ppm A vp lp lf``,
  srw_tac [][FCB_def, NEWFCB_def] >>
  `FINITE A ∧ (∀p. FINITE (supp ppm p))`
     by fsrw_tac [][sidecond_def] >>
  Q_TAC (NEW_TAC "z") `A ∪ GFVl ts ∪ GFVl us ∪ supp ppm p ∪ {a}` >>
  `lf a bv r1 r2 ts us p = lf z bv (listpm (fn_pmact ppm dpm) [(z,a)] r1) r2
                              (gtpml [(z,a)] ts) us p`
     by (fsrw_tac [][NEWFCB_def] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
         first_x_assum match_mp_tac >>
         fsrw_tac [][genind_GLAM_eqn] >> metis_tac []) >>
  pop_assum SUBST1_TAC >>
  match_mp_tac notinsupp_I >>
  qexists_tac `{z} ∪ A ∪ GFVl (gtpml [(z,a)] ts) ∪ GFVl us ∪ supp ppm p` >>
  srw_tac [][perm_supp]>>
  srw_tac [][support_def] >>
  sidecond_tac lhs >>
  `x ∉ supp (list_pmact (fn_pmact ppm dpm)) r2 ∧ y ∉ supp (list_pmact (fn_pmact ppm dpm)) r2 ∧
   x ∉ supp (list_pmact (fn_pmact ppm dpm)) (listpm (fn_pmact ppm dpm) [(z,a)] r1) ∧
   y ∉ supp (list_pmact (fn_pmact ppm dpm)) (listpm (fn_pmact ppm dpm) [(z,a)] r1)`
      by (srw_tac [][perm_supp] >>
          metis_tac [LIST_REL_combined_supps, swapstr_def]) >>
  asm_simp_tac (srw_ss()) [LIST_REL_relsupp_gtpml, genind_GLAM_eqn, supp_fresh,
                           perm_supp] >>
  disch_then match_mp_tac >> fsrw_tac [][genind_GLAM_eqn] >> metis_tac []);

val fresh_I = PROVE_HYP (udplus NEWFCB_OLD) (udplus tmrec_fresh)
val eqv_I = PROVE_HYP (udplus NEWFCB_OLD) (udplus tmrec_equivariant)


fun xmatch_cond_assum dir (asl,w) =
    first_x_assum (fn rwt =>
       mp_tac (PART_MATCH (lhs o #2 o strip_imp)
                          rwt
                          (dir w))) (asl,w)


val parameter_gtm_recursion = store_thm(
"parameter_gtm_recursion",
``sidecond dpm ppm A ^vp ^lp ^vf ^lf ∧ NEWFCB dpm ppm A ^vp ^lp ^lf ⇒
  ∃f.
   ((∀n s vv p. genind vp lp n (GVAR s vv) ⇒ (f (GVAR s vv) p = vf s vv p)) ∧
    ∀n v bv ns ms ts us p.
       v ∉ A ∧ v ∉ supp ppm p ∧ genind vp lp n (GLAM v bv ts us) ⇒
       (f (GLAM v bv ts us) p = lf v bv (MAP f ts) (MAP f us) ts us p)) ∧
   ∀n t p.
     genind vp lp n t ==>
     ∀x y. x ∉ A ∧ y ∉ A ==>
           (pmact dpm [(x,y)] (f t p) = f (gtpm [(x,y)] t) (pmact ppm [(x,y)] p))``,
strip_tac >>
`FINITE A ∧ ∀p. FINITE (supp ppm p)` by fsrw_tac [][sidecond_def] >>
qexists_tac `tmrec A ppm vf lf` >>
reverse conj_tac >-
   (rpt strip_tac >> imp_res_tac eqv_I >> srw_tac [][]) >>
conj_tac >- srw_tac [][tmrec_GVAR] >>
srw_tac [][tmrec_GLAM] >>
DEEP_INTRO_TAC optionTheory.some_intro >>
asm_simp_tac (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
reverse conj_tac >- (
  (* bogus ARB case *)
  asm_simp_tac (srw_ss()) [GLAM_eq_thm] >>
  Q_TAC (NEW_TAC "z") `A ∪ supp ppm p ∪ GFVl ts ∪ GFVl us ∪ {v}` >>
  disch_then (qspec_then `z` mp_tac) >>
  fsrw_tac [][gtpml_eqr] >>
  fsrw_tac [DNF_ss][IN_supp_listpm, MEM_listpm_EXISTS, perm_supp] >>
  metis_tac []) >>
asm_simp_tac (srw_ss()++DNF_ss++ETA_ss) [GLAM_eq_thm,gtpml_eqr,gtpm_eqr] >>
qx_gen_tac `u` >> strip_tac >>
`LIST_REL (relsupp A dpm ppm) ts (MAP (tmrec A ppm vf lf) ts) ∧
 LIST_REL (relsupp A dpm ppm) us (MAP (tmrec A ppm vf lf) us)` by (
  assume_tac fresh_I >>
  fsrw_tac [DNF_ss][MEM_EL] >>
  srw_tac [][LIST_REL_EL_EQN, EL_MAP, relsupp_def] >>
  fsrw_tac [][AND_IMP_INTRO] >>
  first_x_assum match_mp_tac >>
  fsrw_tac [][] >>
  match_mp_tac genind_GLAM_subterm >>
  srw_tac [][MEM_EL] >>
  metis_tac []) >>
asm_simp_tac (srw_ss()) [pmact_flip_args] >>
qsuff_tac `MAP (tmrec A ppm vf lf) (gtpml [(u,v)] ts) =
           listpm (fn_pmact ppm dpm) [(u,v)] (MAP (tmrec A ppm vf lf) ts)`
  >- (disch_then SUBST1_TAC >> fsrw_tac [][NEWFCB_def] >>
      first_x_assum match_mp_tac >> fsrw_tac [][perm_supp] >> metis_tac []) >>
srw_tac [][listpm_tMAP, MAP_EQ_f, MEM_listpm_EXISTS, FUN_EQ_THM,
           fnpm_def] >>
srw_tac [][pmact_sing_inv] >>
assume_tac (eqv_I |> Q.GEN `t`
                  |> SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]) >>
(fn (asl,w) => pop_assum
                   (fn rwt =>
                       mp_tac (PART_MATCH (lhs o #2 o dest_imp) rwt
                                          (rhs w) |> Q.GEN `n`)) (asl,w)) >>
asm_simp_tac (srw_ss()) [pmact_sing_inv] >>
metis_tac [genind_GLAM_subterm]);

val _ = export_theory()
