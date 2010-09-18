(* this is an -*- sml -*- file *)
open HolKernel Parse boolLib

open bossLib binderLib
open basic_swapTheory nomsetTheory
open pred_setTheory
open BasicProvers
open quotientLib
open boolSimps

open lcsymtacs

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before export_rewrites [s])
fun Save_Thm(s, th) = (save_thm(s, th) before export_rewrites [s])

val _ = new_theory "generic_terms"

val _ = computeLib.auto_import_definitions := false

val _ = Hol_datatype `
  pregterm = var of string => 'v
           | lam of string => 'b => pregterm list => pregterm list
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

val ptpm_def = Define`
  (ptpm p (var s vv) = var (perm_of p s) vv) ∧
  (ptpm p (lam v bv bndts unbndts) = lam (perm_of p v)
                                         bv
                                         (ptpml p bndts)
                                         (ptpml p unbndts)) ∧
  (ptpml p [] = []) ∧
  (ptpml p (h::t) = ptpm p h :: ptpml p t)
`;

val ptpml_listpm = store_thm(
  "ptpml_listpm",
  ``∀l. ptpml p l = listpm ptpm p l``,
  Induct >> srw_tac[][ptpm_def]);

val ptpm_thm = Save_Thm(
  "ptpm_thm",
  ptpm_def |> CONJUNCTS |> (fn l => List.take(l, 2)) |> LIST_CONJ
           |> REWRITE_RULE [ptpml_listpm])

val ptpm_nil0 = prove(
  ``(∀t:(α,β)pregterm. ptpm [] t = t) ∧
    (∀l:(α,β)pregterm list. ptpml [] l = l)``,
  ho_match_mp_tac oldind >> srw_tac [][ptpml_listpm])

val ptpm_NIL = Save_Thm(
  "ptpm_NIL",
  CONJUNCT1 ptpm_nil0);

val ptpm_compose0 = prove(
  ``(∀t:(α,β)pregterm. ptpm p1 (ptpm p2 t) = ptpm (p1 ++ p2) t) ∧
    (∀l:(α,β)pregterm list.
        ptpml p1 (ptpml p2 l) = ptpml (p1 ++ p2) l)``,
  ho_match_mp_tac oldind >> srw_tac [][ptpml_listpm, lswapstr_APPEND]);

val permeq_ptpm = prove(
  ``(∀x. lswapstr p1 x = lswapstr p2 x) ⇒
    (∀t:(α,β)pregterm. ptpm p1 t = ptpm p2 t) ∧
    (∀l:(α,β)pregterm list. ptpml p1 l = ptpml p2 l)``,
  strip_tac >> ho_match_mp_tac oldind >> srw_tac [][ptpml_listpm]);

val ptpm_is_perm = Store_Thm(
  "ptpm_is_perm",
  ``is_perm ptpm``,
  srw_tac [][is_perm_def, ptpm_compose0, permeq_def, FUN_EQ_THM,
             permeq_ptpm]);

val ptpm_INVERSE = Store_Thm(
  "ptpm_INVERSE",
  ``(ptpm p (ptpm (REVERSE p) t) = t) /\
    (ptpm (REVERSE p) (ptpm p t) = t)``,
  srw_tac [][is_perm_inverse]);

val ptpm_id_front = Store_Thm(
  "ptpm_id_front",
  ``!x t. ptpm ((x,x)::t) M = ptpm t M``,
  srw_tac [][is_perm_id])

val ptpm_sing_inv = Store_Thm(
  "ptpm_sing_inv",
  ``ptpm [h] (ptpm [h] t) = t``,
  srw_tac [][is_perm_sing_inv]);

val ptpml_sing_inv = prove(
  ``ptpml [h] (ptpml [h] l) = l``,
  srw_tac [ETA_ss][ptpml_listpm, is_perm_sing_inv, is_perm_nil]);

val ptpml_id_front = prove(
  ``ptpml ((x,x)::t) l = ptpml t l``,
  srw_tac [ETA_ss][ptpml_listpm, is_perm_id]);


val ptpm_fv = store_thm(
  "ptpm_fv",
  ``(∀t:(α,β)pregterm. fv (ptpm p t) = ssetpm p (fv t)) ∧
    (∀l:(α,β)pregterm list. fvl (listpm ptpm p l) = ssetpm p (fvl l))``,
  ho_match_mp_tac oldind >> srw_tac[][perm_INSERT, perm_DELETE, perm_UNION]);
val _ = augment_srw_ss [rewrites [ptpm_fv]]

val allatoms_def = Define`
  (allatoms (var s vv) = {s}) ∧
  (allatoms (lam v bv bndts unbndts) =
     v INSERT allatomsl bndts ∪ allatomsl unbndts) ∧
  (allatomsl [] = ∅) ∧
  (allatomsl (t::ts) = allatoms t ∪ allatomsl ts)
`;

val allatoms_finite = Store_Thm(
  "allatoms_finite",
  ``(∀t:(α,β)pregterm. FINITE (allatoms t)) ∧
    (∀l:(α,β)pregterm list. FINITE (allatomsl l))``,
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def]);

val allatoms_supports = store_thm(
  "allatoms_supports",
  ``(∀t:(α,β)pregterm. support ptpm t (allatoms t)) ∧
    (∀l:(α,β)pregterm list. support (listpm ptpm) l (allatomsl l))``,
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
       a ∉ allatomsl l ∧ b ∈ allatomsl l ⇒ listpm ptpm [(a,b)] l ≠ l)``,
  ho_match_mp_tac oldind >> srw_tac [][allatoms_def] >>
  srw_tac [][swapstr_def]);

val allatoms_supp = store_thm(
  "allatoms_supp",
  ``supp ptpm t = allatoms t``,
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
      allatomsl (listpm ptpm p l) = ssetpm p (allatomsl l))``,
  ho_match_mp_tac oldind >>
  srw_tac [][allatoms_def, perm_INSERT, perm_UNION]);

val (aeq_rules, aeq_ind, aeq_cases) = Hol_reln`
  (!s vv. aeq (var s vv) (var s vv)) /\
  (!u v bv z bndts1 bndts2 us1 us2.
      aeql us1 us2 ∧
      aeql (ptpml [(u,z)] bndts1) (ptpml [(v,z)] bndts2) ∧
      z ∉ allatomsl bndts1 ∧ z ∉  allatomsl bndts2 ∧ z ≠ u ∧ z ≠ v ⇒
      aeq (lam u bv bndts1 us1) (lam v bv bndts2 us2)) ∧
  aeql [] [] ∧
  (∀h1 h2 t1 t2. aeq h1 h2 ∧ aeql t1 t2 ⇒ aeql (h1::t1) (h2::t2))
`;

val aeq_lam = List.nth(CONJUNCTS aeq_rules, 1)

val aeq_distinct = store_thm(
  "aeq_distinct",
  ``~aeq (var s vv) (lam v bv ts us)``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][]);

val ptpm_sing_to_back = store_thm(
  "ptpm_sing_to_back",
  ``ptpm [(perm_of p u, perm_of p v)] (ptpm p t) = ptpm p (ptpm [(u,v)] t)``,
  srw_tac [][is_perm_sing_to_back]);

val ptpml_sing_to_back = store_thm(
  "ptpml_sing_to_back",
  ``ptpml [(perm_of p u, perm_of p v)] (ptpml p l) =
    ptpml p (ptpml [(u,v)] l)``,
  srw_tac [][ptpml_listpm, is_perm_sing_to_back])

val aeq_ptpm_lemma = store_thm(
  "aeq_ptpm_lemma",
  ``(!t:(α,β)pregterm u. aeq t u ==> !p. aeq (ptpm p t) (ptpm p u)) ∧
    (∀ts:(α,β)pregterm list us.
      aeql ts us ⇒ ∀π. aeql (listpm ptpm π ts) (listpm ptpm π us)) ``,
  ho_match_mp_tac aeq_ind >> srw_tac [][aeq_rules, ptpml_listpm] >>
  match_mp_tac aeq_lam >>
  Q.EXISTS_TAC `lswapstr p z` THEN
  srw_tac [][allatoms_perm, ptpm_sing_to_back, perm_IN,
             ptpml_listpm, is_perm_sing_to_back]);

val aeq_ptpm_eqn = store_thm(
  "aeq_ptpm_eqn",
  ``aeq (ptpm p t) u = aeq t (ptpm (REVERSE p) u)``,
  METIS_TAC [aeq_ptpm_lemma, ptpm_INVERSE]);

val aeql_ptpm_eqn = store_thm(
  "aeql_ptpm_eqn",
  ``aeql (listpm ptpm p l1) l2 = aeql l1 (listpm ptpm p⁻¹ l2)``,
  METIS_TAC [aeq_ptpm_lemma, is_perm_inverse, ptpm_is_perm, listpm_is_perm]);

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
  srw_tac [][EXTENSION, ptpm_fv, perm_IN, ptpml_listpm] THEN
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

val aeq_refl = Store_Thm(
  "aeq_refl",
  ``(∀t:(α,β)pregterm. aeq t t) ∧ (∀l:(α,β)pregterm list. aeql l l)``,
  ho_match_mp_tac oldind >> asm_simp_tac (srw_ss())[aeq_rules] >>
  REPEAT gen_tac >> strip_tac >>
  MAP_EVERY Q.X_GEN_TAC [`b`, `s`] >>
  MATCH_MP_TAC aeq_lam >>
  SRW_TAC [][aeql_ptpm_eqn, ptpml_listpm] THEN
  srw_tac [][ptpm_nil0, GSYM ptpml_listpm] >>
  Q.SPEC_THEN `s INSERT allatomsl l` MP_TAC NEW_def THEN SRW_TAC [][] THEN
  METIS_TAC []);

val ptpm_flip_args = store_thm(
  "ptpm_flip_args",
  ``!x y t. ptpm ((y,x)::t) M = ptpm ((x,y)::t) M``,
  srw_tac [][is_perm_flip_args]);

val ptpml_flip_args = prove(
  ``ptpml ((y,x)::t) l = ptpml ((x,y)::t) l``,
  srw_tac [][is_perm_flip_args, ptpml_listpm]);

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

val aeq_ptm_11 = store_thm(
  "aeq_ptm_11",
  ``(aeq (var s1 vv1) (var s2 vv2) = (s1 = s2) ∧ (vv1 = vv2)) /\
    (aeq (lam v bv1 bndts1 unbndts1) (lam v bv2 bndts2 unbndts2) =
      (bv1 = bv2) ∧ aeql bndts1 bndts2 ∧ aeql unbndts1 unbndts2)``,
  SRW_TAC [][aeq_lam_inversion, aeq_ptpm_eqn, aeq_var_inversion, EQ_IMP_THM]
  THENL [
    full_simp_tac (srw_ss() ++ ETA_ss) [aeql_ptpm_eqn, ptpml_listpm,
                                                  is_perm_nil],
    srw_tac [][],
    Q_TAC (NEW_TAC "z") `v INSERT allatomsl bndts1 ∪ allatomsl bndts2` THEN
    Q.EXISTS_TAC `z` >>
    srw_tac [ETA_ss][aeql_ptpm_eqn, ptpml_listpm, is_perm_nil]
  ]);

val ptpml_sing_to_back' = prove(
  ``ptpml p (ptpml [(u,v)] tl) =
       ptpml [(lswapstr p u, lswapstr p v)] (ptpml p tl)``,
  simp_tac (srw_ss()) [ptpml_listpm, is_perm_sing_to_back]);

val ptpml_fresh =
  allatoms_supports |> CONJUNCT2 |>
  SIMP_RULE (srw_ss()) [support_def, GSYM ptpml_listpm]

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
       by FULL_SIMP_TAC (srw_ss()) [aeql_ptpm_eqn, ptpml_listpm] THEN
    POP_ASSUM
       (Q.SPEC_THEN `ptpml [(z,d)] bt3`
           (ASSUME_TAC o Q.GEN `bt3` o
            SIMP_RULE (srw_ss()) [GSYM ptpml_listpm] o
            SIMP_RULE (srw_ss() ++ ETA_ss)
                      [ptpml_listpm, is_perm_sing_inv, is_perm_nil])) THEN
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ptpml_sing_to_back']) THEN
    SRW_TAC [][swapstr_def, ptpml_fresh] THEN
    `aeql (ptpml [(z2,d)] (ptpml [(v,z2)] bt2))
          (ptpml [(z2,d)] (ptpml [(w,z2)] bt3))`
       by (srw_tac [ETA_ss]
                   [Once aeql_ptpm_eqn, ptpml_listpm, is_perm_nil] >>
           srw_tac [][GSYM ptpml_listpm]) >>
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ptpml_sing_to_back']) THEN
    SRW_TAC [][swapstr_def, ptpml_fresh] THEN
    `aeql (ptpml [(u,d)] bt1) (ptpml [(w,d)] bt3)` by METIS_TAC [] THEN
    METIS_TAC [aeq_lam],

    srw_tac [][],
    rpt gen_tac >> strip_tac >> gen_tac >>
    srw_tac [][Once aeq_cases, SimpL ``$==>``] >>
    metis_tac [aeq_rules]
  ]);

open relationTheory
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

val aeql_ptpm_eqn' = REWRITE_RULE [GSYM ptpml_listpm] aeql_ptpm_eqn

val fresh_swap = store_thm(
  "fresh_swap",
  ``(∀t:(α,β)pregterm x y. x ∉ fv t ∧ y ∉ fv t ⇒ aeq t (ptpm [(x, y)] t)) ∧
    (∀l:(α,β)pregterm list x y.
       x ∉ fvl l ∧ y ∉ fvl l ⇒ aeql l (ptpml [(x,y)] l))``,
  ho_match_mp_tac oldind >>
  asm_simp_tac (srw_ss()) [aeq_rules, ptpm_nil0, ptpm_def] >>
  map_every qx_gen_tac [`bt`, `ut`] >> strip_tac >>
  map_every qx_gen_tac [`b`, `s`,`x`,`y`] >>
  strip_tac >> srw_tac [][] >>
  match_mp_tac alt_aeq_lam >> rpt strip_tac >>
  srw_tac [][ptpml_id_front, ptpm_nil0] >>
  `z ∉ fvl bt` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] >| [
    Cases_on `s = x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      ONCE_REWRITE_TAC [GSYM ptpml_sing_to_back] THEN
      SRW_TAC [][swapstr_def, aeql_ptpm_eqn', ptpml_sing_inv,
                 ptpml_id_front, ptpm_nil0],
      ALL_TAC
    ] THEN Cases_on `s = y` THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      ONCE_REWRITE_TAC [GSYM ptpml_sing_to_back] THEN
      SRW_TAC [][swapstr_def, ptpml_flip_args, aeql_ptpm_eqn',
                 ptpml_sing_inv],
      SRW_TAC [][swapstr_def, aeql_ptpm_eqn', ptpml_sing_inv]
    ],
    Cases_on `s = x` THEN1 SRW_TAC [][ptpml_id_front, ptpm_nil0] THEN
    ONCE_REWRITE_TAC [GSYM ptpml_sing_to_back] THEN
    SRW_TAC [][swapstr_def, ptpml_flip_args, aeql_ptpm_eqn', ptpml_sing_inv],
    Cases_on `s = y` THEN1 SRW_TAC [][ptpml_id_front, ptpm_nil0] THEN
    ONCE_REWRITE_TAC [GSYM ptpml_sing_to_back] THEN
    SRW_TAC [][swapstr_def, aeql_ptpm_eqn', ptpml_sing_inv]
  ]);

val lam_aeq_thm = store_thm(
  "lam_aeq_thm",
  ``aeq (lam v1 bv1 t1 u1) (lam v2 bv2 t2 u2) =
       (v1 = v2) ∧ (bv1 = bv2) ∧ aeql t1 t2 ∧ aeql u1 u2 ∨
       v1 ≠ v2 ∧ (bv1 = bv2) ∧ v1 ∉ fvl t2 ∧ aeql t1 (ptpml [(v1,v2)] t2) ∧
       aeql u1 u2``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, DISJ_IMP_THM] THEN REPEAT CONJ_TAC THENL [
    srw_tac [][aeq_lam_inversion] >>
    `z ∉ fvl t1 ∧ z ∉ fvl t2`
       by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] >>
    Cases_on `v1 = v2` >- fsrw_tac [][aeql_ptpm_eqn', ptpml_sing_inv] THEN
    `v1 ∉ fvl t2`
        by (strip_tac >>
            `v1 ∈ fvl (ptpml [(v2,z)] t2)`
               by SRW_TAC [][ptpm_fv, perm_IN, ptpml_listpm] THEN
            `v1 ∈ fvl (ptpml [(v1,z)] t1)` by metis_tac [aeq_fv] THEN
            fsrw_tac [][ptpm_fv, perm_IN, ptpml_listpm]) >>
    fsrw_tac [][aeql_ptpm_eqn'] >>
    Q.PAT_ASSUM `aeql X (ptpml PI Y)` MP_TAC THEN
    SRW_TAC [][swapstr_def, Once ptpml_sing_to_back'] THEN
    MATCH_MP_TAC (MP_CANON (CONJUNCT2 aeq_trans)) THEN
    Q.EXISTS_TAC `ptpml [(v1,v2)] (ptpml [(v1,z)] t2)`  THEN
    FULL_SIMP_TAC (srw_ss()) [ptpml_flip_args, aeql_ptpm_eqn', fresh_swap,
                              ptpml_sing_inv],

    srw_tac [][] >> match_mp_tac alt_aeq_lam >>
    srw_tac [][aeql_ptpm_eqn', ptpml_sing_inv],

    srw_tac [][] >> match_mp_tac alt_aeq_lam >>
    srw_tac [][aeql_ptpm_eqn'] >>
    `z ∉ fvl t2` by metis_tac [SUBSET_DEF, fv_SUBSET_allatoms] >>
    SRW_TAC [][swapstr_def, ptpm_flip_args, Once ptpml_sing_to_back'] >>
    match_mp_tac (MP_CANON (CONJUNCT2 aeq_trans)) >>
    qexists_tac `ptpml [(v1,v2)] t2` >>
    srw_tac [][aeql_ptpm_eqn', fresh_swap, ptpml_sing_inv, ptpml_flip_args]
  ]);

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
  srw_tac [][aeql_ptpm_eqn', ptpml_sing_inv] >>
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
    {def_name = s ^ "_def", fixity = Prefix, fname = s, func = t};

val ptpm_fv' =
    ptpm_fv |> CONJUNCT1 |> REWRITE_RULE [EXTENSION]
            |> CONV_RULE
                 (STRIP_QUANT_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [perm_IN])))

val fvl_MAP = prove(
  ``fvl l = BIGUNION (set (MAP fv l))``,
  Induct_on `l` >> srw_tac [][]);
val rmfvl = REWRITE_RULE [fvl_MAP]

val ptpml_MAP = prove(
  ``ptpml p l = MAP (ptpm p) l``,
  Induct_on `l` >> srw_tac [][ptpm_def]);
val rmptpml = REWRITE_RULE [ptpml_MAP]

fun front n l = List.take (l, n)
fun drop n l = List.drop(l,n)

val fvl_eqrespects = prove(
  ``∀ts1 ts2:(α,β) pregterm list. (ts1 = ts2) ==> (fvl ts1 = fvl ts2)``,
  srw_tac [][]);


val [GFV_thm0, gfvl_thm, GFV_gtpm, simple_induction0, gtpm_thm,
     gterm_distinct, gterm_11,
     GLAM_eq_thm, FRESH_swap0,
     FINITE_GFV,
     gtpm_sing_inv, gtpm_NIL, gtpm_inverse, gtpm_flip_args, gtpm_id_front,
     gtpm_compose, gtpm_permeq] =
    quotient.define_quotient_types_full
    {
     types = [{name = "gterm", equiv = aeq_equiv}],
     defs = map mk_def
       [("GLAM", ``lam:string -> α -> (α,β)pregterm list ->
                       (α,β)pregterm list -> (α,β)pregterm``),
        ("GVAR", ``var:string -> β -> (α,β)pregterm``),
        ("GFV", ``fv : (α,β)pregterm -> string set``),
        ("gfvl", ``fvl : (α,β)pregterm list -> string set``),
        ("gtpm", ``ptpm : (string # string) list -> (α,β)pregterm ->
                          (α,β)pregterm``)],
     tyop_equivs = [],
     tyop_quotients = [],
     tyop_simps = [],
     respects = [rmaeql lam_respects_aeq,
                 var_respects_aeq, CONJUNCT1 aeq_fv,
                 rmaeql (CONJUNCT2 aeq_fv),
                 aeq_ptpm_lemma |> CONJUNCT1
                                |> SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM]
                 ],
     poly_preserves = [],
     poly_respects = [],
     old_thms = [fv_def |> CONJUNCTS |> front 2 |> LIST_CONJ,
                 fv_def |> CONJUNCTS |> drop 2 |> LIST_CONJ,
                 ptpm_fv', pind,
                 ptpm_def |> CONJUNCTS |> front 2 |> LIST_CONJ |> rmptpml,
                 aeq_distinct, rmaeql aeq_ptm_11,
                 rmptpml (rmaeql lam_aeq_thm), CONJUNCT1 fresh_swap,
                 finite_fv,
                 ptpm_sing_inv, ptpm_NIL, ptpm_INVERSE,
                 ptpm_flip_args,
                 ptpm_id_front, CONJUNCT1 ptpm_compose0,
                 permeq_ptpm |> UNDISCH |> CONJUNCT1 |> DISCH_ALL]}

val simple_induction = save_thm(
  "simple_induction",
  REWRITE_RULE [listTheory.EVERY_MEM] simple_induction0)

val gfvl_BIGUNION = prove(
  ``gfvl ts = BIGUNION (set (MAP GFV ts))``,
  Induct_on `ts` >> srw_tac [][gfvl_thm])

val rmgfvl = REWRITE_RULE [gfvl_BIGUNION]

(* don't export any of these, because the intention is not to have users
   working with this type *)
val GFV_thm = save_thm("GFV_thm", rmgfvl GFV_thm0)
val GFV_gtpm = save_thm("GFV_gtpm", GFV_gtpm)
val gtpm_thm = save_thm("gtpm_thm", gtpm_thm)
val gterm_distinct = save_thm("gterm_distinct", gterm_distinct)
val gterm_11 = save_thm("gterm_11", gterm_11)
val GLAM_eq_thm = save_thm("GLAM_eq_thm", rmgfvl GLAM_eq_thm)
val gtpm_fresh = save_thm("gtpm_fresh", GSYM FRESH_swap0)
val FINITE_GFV = save_thm("FINITE_GFV", FINITE_GFV)
val gtpm_sing_inv = save_thm("gtpm_sing_inv", gtpm_sing_inv);
val gtpm_NIL  = save_thm("gtpm_NIL", gtpm_NIL );
val gtpm_inverse  = save_thm("gtpm_inverse", gtpm_inverse);
val gtpm_flip_args  = save_thm("gtpm_flip_args", gtpm_flip_args );
val gtpm_id_front = save_thm("gtpm_id_front", gtpm_id_front);
val gtpm_compose = save_thm("gtpm_compose", gtpm_compose)
val gtpm_permeq = save_thm("gtpm_permeq", gtpm_permeq)

val gtpm_is_perm = store_thm(
  "gtpm_is_perm",
  ``is_perm gtpm``,
  srw_tac [][is_perm_def,gtpm_NIL,gtpm_compose, permeq_def, FUN_EQ_THM,
             gtpm_permeq]);

val _ = augment_srw_ss [rewrites [gtpm_is_perm]]

val _ = delete_const "gfvl"
val _ = delete_const "fv"

val MAP_EQ1 = prove(
  ``(MAP f l = l) ⇔ ∀x. MEM x l ⇒ (f x = x)``,
  Induct_on `l` >> srw_tac [][DISJ_IMP_THM, FORALL_AND_THM]);

val MEM_MAP = listTheory.MEM_MAP
val MEM_EL = listTheory.MEM_EL


(* default rewriting of negations makes a mess of these. *)
val NOT_IN_GFV = store_thm(
  "NOT_IN_GFV",
  ``(x ∉ GFV (GVAR s vv) ⇔ x ≠ s) ∧
    (x ∉ GFV (GLAM v bv ts us) ⇔
       (∀u. MEM u us ⇒ x ∉ GFV u) ∧
       (∀t. x ≠ v ∧ MEM t ts ⇒ x ∉ GFV t))``,
  srw_tac [][GFV_thm, MEM_MAP] >> metis_tac []);

val GFV_apart = store_thm(
  "GFV_apart",
  ``∀t x y. x ∈ GFV t ∧ y ∉ GFV t ⇒ gtpm [(x,y)] t ≠ t``,
  ho_match_mp_tac simple_induction >>
  srw_tac [][GFV_thm, gtpm_thm, gterm_11, MEM_MAP,
             MAP_EQ1, GLAM_eq_thm, NOT_IN_GFV]
  >- (Cases_on `y = v` >> srw_tac [][] >> metis_tac [])
  >- (Cases_on `y = v` >> srw_tac [][] >> metis_tac [])
  >- metis_tac []
  >- metis_tac [])

val GFV_support = store_thm(
  "GFV_support",
  ``support gtpm t (GFV t)``,
  srw_tac [][support_def, gtpm_fresh])

(* tempting to delete GFV and just use supp gtpm.... *)
val GFV_supp = store_thm(
  "GFV_supp",
  ``supp gtpm t = GFV t``,
  match_mp_tac (GEN_ALL supp_unique_apart) >>
  srw_tac [][GFV_support, GFV_apart, FINITE_GFV]);

val GLAM_NIL_EQ = store_thm(
  "GLAM_NIL_EQ",
  ``(GLAM u bv1 [] ts = GLAM v bv2 [] ts') ⇔ (bv1 = bv2) ∧ (ts = ts')``,
  srw_tac [][GLAM_eq_thm] >> metis_tac []);

val IN_supp_listpm = prove(
  ``a ∈ supp (listpm pm) l ⇔ ∃e. MEM e l ∧ a ∈ supp pm e``,
  Induct_on `l` >> srw_tac [DNF_ss][]);

val NOT_IN_supp_listpm = prove(
  ``a ∉ supp (listpm pm) l ⇔ ∀e. MEM e l ⇒ a ∉ supp pm e``,
  metis_tac [IN_supp_listpm])

val list_rel_split = prove(
  ``LIST_REL (λx y. P x y ∧ Q x y) l1 l2 ⇔
      LIST_REL P l1 l2 ∧ LIST_REL Q l1 l2``,
  qid_spec_tac `l2` >> Induct_on `l1` >> Cases_on `l2` >> srw_tac [][] >>
  metis_tac []);

val LIST_REL_ind = listTheory.LIST_REL_ind
val LIST_REL_rules = listTheory.LIST_REL_rules
val LIST_REL_EL_EQN = listTheory.LIST_REL_EL_EQN

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

val EVERY_AND = prove(
  ``EVERY (λx. P x ∧ Q x) l ⇔ EVERY P l ∧ EVERY Q l``,
  Induct_on `l` >> srw_tac [][] >> metis_tac []);

val genind_gtpm = store_thm(
  "genind_gtpm",
  ``∀n t. genind vp lp n t ⇒ ∀pi. genind vp lp n (gtpm pi t)``,
  Induct_on `genind` >>
  srw_tac [DNF_ss][gtpm_thm, genind_rules, list_rel_split] >>
  match_mp_tac (List.nth(grules', 1)) >>
  fsrw_tac [CONJ_ss][LIST_REL_EL_EQN, listTheory.EL_MAP] >>
  metis_tac [])

val genind_gtpm_eqn = store_thm(
  "genind_gtpm_eqn",
  ``genind vp lp n (gtpm pi t) = genind vp lp n t``,
  metis_tac [gtpm_inverse, genind_gtpm]);
val _ = augment_srw_ss [rewrites [genind_gtpm_eqn]]

val LIST_REL_genind_gtpm_eqn = store_thm(
  "LIST_REL_genind_gtpm_eqn",
  ``LIST_REL (genind vp lp) ns (listpm gtpm pi ts) =
    LIST_REL (genind vp lp) ns ts``,
  qid_spec_tac `ns` >> Induct_on `ts` >> Cases_on `ns` >>
  srw_tac [][]);

val _ = augment_srw_ss [rewrites [FINITE_GFV]]

val finite_gfvl = prove(
  ``FINITE (BIGUNION (set (MAP GFV ts)))``,
  Induct_on `ts` >> srw_tac [][MEM_MAP] >> srw_tac [][]);

val _ = augment_srw_ss [rewrites [finite_gfvl]]
val _ = overload_on ("gfvl", ``λts. BIGUNION (set (MAP GFV ts))``)

val not_in_gfvl = prove(
  ``s ∉ gfvl ts ⇔ ∀t. MEM t ts ⇒ s ∉ GFV t``,
  srw_tac [][MEM_MAP] >> metis_tac []);

val gfvl_supp = prove(
  ``gfvl ts = supp (listpm gtpm) ts``,
  Induct_on `ts` >> srw_tac [][GFV_supp]);

val finite_gfvlsupp = prove(
  ``FINITE (supp (listpm gtpm) x)``,
  srw_tac [][GSYM gfvl_supp]);
val _ = augment_srw_ss [rewrites [finite_gfvlsupp]]

val MAP_gtpm = prove(
  ``MAP (gtpm pi) l = listpm gtpm pi l``,
  Induct_on `l` >> srw_tac [][]);

val bvc_genind = store_thm(
  "bvc_genind",
  ``∀P fv.
      (∀x. FINITE (fv x)) ∧
      (∀n s vv x. vp n vv ⇒ P n (GVAR s vv) x) ∧
      (∀n v bv tns uns ts us x.
         LIST_REL (λn t. genind vp lp n t ∧ ∀x. P n t x) tns ts ∧
         LIST_REL (λn t. genind vp lp n t ∧ ∀x. P n t x) uns us ∧
         lp n bv tns uns ∧ v ∉ fv x ∧ v ∉ supp (listpm gtpm) us
        ⇒
         P n (GLAM v bv ts us) x)
   ⇒
      ∀n t. genind vp lp n t ⇒ ∀x. P n t x``,
  rpt GEN_TAC >> strip_tac >>
  qsuff_tac `∀n t. genind vp lp n t ⇒ ∀pi x. P n (gtpm pi t) x`
  >- metis_tac [gtpm_NIL] >>
  Induct_on `genind` >> srw_tac [DNF_ss][gtpm_thm, list_rel_split] >>
  Q_TAC (NEW_TAC "z")
    `fv x ∪ {lswapstr pi v; v} ∪ supp (listpm gtpm) (MAP (gtpm pi) us) ∪
     supp (listpm gtpm) (MAP (gtpm pi) ts)` >>
  `GLAM (lswapstr pi v) bv (MAP (gtpm pi) ts) (MAP (gtpm pi) us) =
   GLAM z bv (listpm gtpm [(z,lswapstr pi v)] (MAP (gtpm pi) ts))
             (MAP (gtpm pi) us)`
     by (srw_tac [][GLAM_eq_thm, not_in_gfvl]
         >- (fsrw_tac [][GSYM MAP_gtpm, MEM_MAP, NOT_IN_supp_listpm] >>
             fsrw_tac [DNF_ss][GFV_supp, GFV_gtpm]) >>
         srw_tac [ETA_ss][MAP_gtpm, is_perm_flip_args, is_perm_nil]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum match_mp_tac >>
  map_every qexists_tac [`tns`, `uns`] >>
  asm_simp_tac (srw_ss() ++ DNF_ss) [MEM_MAP, GSYM MAP_gtpm] >>
  fsrw_tac [CONJ_ss][LIST_REL_EL_EQN, listTheory.EL_MAP] >>
  srw_tac [][gtpm_compose])

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
       v ∉ supp (listpm gtpm) us ⇒
       Q (GLAM v bv ts us) x) ⇔
   (∀v bv ts us x.
      (∀t x. MEM t ts ⇒ Q t x) ∧ (∀u x. MEM u us ⇒ Q u x) ∧
      v ∉ fv x ∧ v ∉ supp (listpm gtpm) us ⇒
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


val vf = mk_var ("vf", ``: string -> β -> γ``)
val lf = mk_var ("lf", ``: string -> α -> γ list -> (α,β)gterm list ->
                           γ list -> (α,β)gterm list -> γ``)

val _ = temp_set_fixity "-p->" (Infixr 490)
val _ = temp_overload_on ("-p->", ``fnpm``)



val vfpm = ``(lswapstr -p-> K I -p-> dpm) π ^vf`` |> rator |> rator
val lfpm = ``(lswapstr -p-> K I -p-> listpm dpm -p-> listpm gtpm -p->
              listpm dpm -p-> listpm gtpm -p-> dpm) π ^lf``
               |> rator |> rator

val vp = ``vp: num -> β -> bool``
val lp = ``lp: num -> α -> num list -> num list -> bool``

val permsupp_sidecond =
  ``is_perm dpm ∧ FINITE A ∧
    (∀x y n s vv.
       x ∉ A ∧ y ∉ A ∧ ^vp n vv ==>
       (dpm [(x,y)] (^vf s vv) = ^vf (lswapstr [(x,y)] s) vv)) ∧
    (∀x y n s bv ds1 ts ds2 us ns ms.
       x ∉ A ∧ y ∉ A ∧ ^lp n bv ns ms ∧
       LIST_REL (genind ^vp ^lp) ns ts ∧
       LIST_REL (genind ^vp ^lp) ms us ==>
       (dpm [(x,y)] (^lf s bv ds1 ts ds2 us) =
        ^lf (lswapstr [(x,y)] s) bv
            (listpm dpm [(x,y)] ds1)
            (listpm gtpm [(x,y)] ts)
            (listpm dpm [(x,y)] ds2)
            (listpm gtpm [(x,y)] us)))``

val FCB = ``∀a n ts us ms ns ds1 ds2 bv.
             a ∉ A ∧ a ∉ supp (listpm gtpm) us ∧
             ^lp n bv ns ms ∧
             LIST_REL (genind ^vp ^lp) ns ts ∧
             LIST_REL (genind ^vp ^lp) ms us ==>
             a ∉ supp dpm (^lf a bv ds1 ts ds2 us)``



val (recn_rel_rules, recn_rel_ind, recn_rel_cases) = Hol_reln`
  (∀s vv n. ^vp n vv ==> recn_rel ^vf ^lf ^vp ^lp A (GVAR s vv) (^vf s vv)) ∧
  (∀bv n ts ns us ms v ds1 ds2.
     LIST_REL (recn_rel ^vf ^lf ^vp ^lp A) ts ds1 ∧
     LIST_REL (recn_rel ^vf ^lf ^vp ^lp A) us ds2 ∧ v ∉ A ∧
     LIST_REL (genind ^vp ^lp) ns ts ∧
     LIST_REL (genind ^vp ^lp) ms us ∧ lp n bv ns ms ∧
     v ∉ supp (listpm gtpm) us ==>
     recn_rel vf lf ^vp ^lp A (GLAM v bv ts us) (lf v bv ds1 ts ds2 us))
`

val recnrel = ``recn_rel ^vf ^lf ^vp ^lp A``
val gind = ``genind ^vp ^lp``

val LIST_REL_exists = prove(
  ``∀ts. (∃ds. LIST_REL R ts ds) ⇔ (∀t. MEM t ts ⇒ ∃r. R t r)``,
  gen_tac >> EQ_TAC >| [
    strip_tac >> pop_assum mp_tac >> map_every qid_spec_tac [`ds`, `ts`] >>
    ho_match_mp_tac LIST_REL_ind >> srw_tac [][] >> metis_tac [],
    Induct_on `ts` >> srw_tac [][] >- metis_tac [LIST_REL_rules] >>
    fsrw_tac [DNF_ss][] >> metis_tac [LIST_REL_rules]
  ]);

(* UB Lemma 4 *)
val recn_rel_exists = prove(
  ``FINITE A ==>
    ∀n t. ^gind n t ==> ∃r. ^recnrel t r``,
  strip_tac >> ho_match_mp_tac genindX >> qexists_tac `A` >> srw_tac [][] >| [
    metis_tac [recn_rel_rules],
    fsrw_tac [ETA_ss][list_rel_split, vacuous_list_rel] >>
    `(∃ds1. LIST_REL ^recnrel ts ds1) ∧ (∃ds2. LIST_REL ^recnrel us ds2)`
          by srw_tac [][LIST_REL_exists] >>
    metis_tac [recn_rel_rules]
  ]);

val recnrel_genind = prove(
  ``∀t r. ^recnrel t r ==> ∃n. ^gind n t``,
  Induct_on `recn_rel` >> metis_tac [genind_rules]);

fun type_to_pm ty = let
  val pm_ty = ``:^ty pm``
in
  case Lib.total dest_vartype ty of
    SOME varname => if varname = "'c" then mk_var("dpm", pm_ty)
                    else ``K I : ^(ty_antiq pm_ty)``
  | NONE => let
      val {Thy,Tyop,Args} = dest_thy_type ty
    in
      case (Thy,Tyop) of
        ("list", "list") => if Args = [``:char``] then ``lswapstr``
                            else ``listpm ^(type_to_pm (hd Args))``
      | ("min", "fun") => let
          val d_t = type_to_pm (hd Args)
          val r_t = type_to_pm (hd (tl Args))
        in
          ``fnpm ^d_t ^r_t``
        end
      | ("generic_terms", "gterm") => mk_const("gtpm", pm_ty)
      | _ => raise mk_HOL_ERR "generic_terms" "type_to_pm"
                              ("Can't do type ("^Thy^"$"^Tyop^")")
    end
end

fun conj1_assum (asl,g) = let
  val (c1, c2) = dest_conj g
  fun f [th1, th2] = CONJ th1 (PROVE_HYP th1 th2)
in
  ([(asl,c1), (c1::asl, c2)], f)
end

fun finitesupp_fnapp (asl, g) = let
  val (supp_pm_t, fx_t) = dest_comb (rand g)
  val rpm = rand supp_pm_t
  val (f_t, x_t) = dest_comb fx_t
  val (dty, rty) = dom_rng (type_of f_t)
  val dpm = type_to_pm dty
  val tytheta = [alpha |-> dty, beta |-> rty]
  val tmtheta = [mk_var("dpm", ``:^dty pm``) |-> dpm,
                 mk_var("rpm", ``:^rty pm``) |-> rpm,
                 mk_var("f", type_of f_t) |-> f_t,
                 mk_var("x", type_of x_t) |-> x_t]
  val th = supp_fnapp |> INST_TYPE tytheta |> INST tmtheta
in
  match_mp_tac pred_setTheory.SUBSET_FINITE_I >>
  EXISTS_TAC (rand (rand (concl th))) >>
  CONV_TAC (LAND_CONV (REWR_CONV FINITE_UNION)) >>
  conj1_assum >| [
    ALL_TAC,
    POP_ASSUM STRIP_ASSUME_TAC >> match_mp_tac th >>
    ASM_SIMP_TAC bool_ss []
  ]
end (asl, g)

val sub_cpos = prove(``∀x s t. s ⊆ t ∧ x ∉ t ⇒ x ∉ s``, metis_tac [SUBSET_DEF])
fun notinsupp_fnapp (asl, g) = let
  val g' = dest_neg g
  val supp_t = rand g'
  val (supp_pm_t, fx_t) = dest_comb supp_t
  val rpm = rand supp_pm_t
  val (f,x) = dest_comb fx_t
  val (dty, rty) = dom_rng (type_of f)
  val dpm = type_to_pm dty
  val tytheta = [alpha |-> dty, beta |-> rty]
  val tmtheta = [mk_var("dpm", ``:^dty pm``) |-> dpm,
                 mk_var("rpm", ``:^rty pm``) |-> rpm,
                 mk_var("f", type_of f) |-> f,
                 mk_var("x", type_of x) |-> x]
  val th = supp_fnapp |> INST_TYPE tytheta |> INST tmtheta
in
  match_mp_tac sub_cpos >> EXISTS_TAC (rand (rand (concl th))) >>
  conj_tac >| [match_mp_tac th, simp_tac (srw_ss()) [IN_UNION]]
end (asl, g)

val little_lemma = prove(
  ``∀ts ds. LIST_REL (λt r. FINITE (supp dpm r)) ts ds ==>
            FINITE (supp (listpm dpm) ds)``,
  ho_match_mp_tac LIST_REL_ind >> srw_tac [][])

(* UB Lemma 5 *)
val recn_rel_finite_support = prove(
  ``^permsupp_sidecond ∧ ^FCB ==>
    ∀t r. ^recnrel t r ==> FINITE (supp dpm r)``,
  strip_tac >> Induct_on `recn_rel` >> srw_tac [][]
  >- (`support dpm (vf s vv) (A ∪ {s})`
        by (srw_tac [][support_def]>>
            `lswapstr [(x,y)] s = s` by srw_tac [][] >>
            metis_tac []) >>
      `FINITE (A ∪ {s})` by srw_tac [][] >>
      metis_tac [supp_smallest, SUBSET_FINITE]) >>
  match_mp_tac (MP_CANON (GEN_ALL supp_absence_FINITE)) >>
  qexists_tac `v` >> metis_tac []);

val list_rel_finitesupp = prove(
  ``^permsupp_sidecond ∧ ^FCB ⇒
    ∀ts ds. LIST_REL ^recnrel ts ds ⇒ FINITE (supp (listpm dpm) ds)``,
  strip_tac >> Induct_on `LIST_REL` >> srw_tac [][] >>
  match_mp_tac (MP_CANON recn_rel_finite_support) >>
  prove_tac []);

val [rvar, rlam] = CONJUNCTS (SIMP_RULE bool_ss [FORALL_AND_THM] recn_rel_rules)

val LENGTH_listpm = prove(
  ``LENGTH (listpm pm π l) = LENGTH l``,
  Induct_on `l` >> srw_tac [][])

val EL_listpm = prove(
  ``∀n l. n < LENGTH l ⇒ (EL n (listpm pm π l) = pm π (EL n l))``,
  Induct >> Cases_on `l` >> srw_tac [][]);

val IN_supp_listpm = prove(
  ``a ∈ supp (listpm pm) l ⇔ ∃e. MEM e l ∧ a ∈ supp pm e``,
  Induct_on `l` >> srw_tac [][] >> metis_tac []);
val NOT_IN_supp_listpm = prove(
  ``a ∉ supp (listpm pm) l ⇔ ∀e. MEM e l ⇒ a ∉ supp pm e``,
  metis_tac [IN_supp_listpm])

val LIST_REL_forall = prove(
  ``LIST_REL (λa b. ∀x. P a b x) l1 l2 ⇔
    ∀x. LIST_REL (λa b. P a b x) l1 l2``,
  qid_spec_tac `l2` >> Induct_on `l1` >> Cases_on `l2` >>
  srw_tac [][FORALL_AND_THM]);

val LIST_REL_listpm = prove(
  ``∀l1 l2.
      (LIST_REL R (listpm pm pi l1) l2 ⇔ LIST_REL (R o pm pi) l1 l2) ∧
      (LIST_REL R l1 (listpm pm' pi l2) ⇔
         LIST_REL (combin$C ($o o R) (pm' pi)) l1 l2)``,
  Induct >> Cases_on `l2` >> srw_tac [][]);

(* ub Lemma 6 *)
val recn_rel_equivariant = prove(
  ``^permsupp_sidecond ==>
    ∀t r. ^recnrel t r ==>
          ∀x y. x ∉ A ∧ y ∉ A ⇒
                recn_rel vf lf vp lp A
                         (gtpm [(x,y)] t) (dpm [(x,y)] r)``,
  strip_tac >> Induct_on `recn_rel` >> srw_tac [][gtpm_thm, MAP_gtpm]
  >- (`dpm [(x,y)] (vf s vv) = vf (lswapstr [(x,y)] s) vv`
       by metis_tac [] >>
      srw_tac [][] >> match_mp_tac rvar >> metis_tac []) >>
  first_x_assum (qspecl_then [`x`,`y`,`n`,`v`,`bv`,`ds1`,`ts`, `ds2`,
                              `us`, `ns`, `ms`] MP_TAC) >>
  srw_tac [][] >> match_mp_tac rlam >>
  map_every qexists_tac [`n`, `ns`, `ms`] >>
  asm_simp_tac (srw_ss())[perm_supp, perm_IN] >>
  fsrw_tac [ETA_ss][list_rel_split, LIST_REL_forall, LIST_REL_listpm] >>
  asm_simp_tac (srw_ss() ++ ETA_ss) [combinTheory.C_DEF, combinTheory.o_DEF]>>
  rpt (first_x_assum (qspecl_then [`x`, `y`] mp_tac)) >> srw_tac [][] >>
  srw_tac [][swapstr_def]);

(* UB Lemma 7 *)
val freshness = prove(
  ``^permsupp_sidecond ∧ ^FCB ⇒
    ∀t r. ^recnrel t r ⇒ ∀a. a ∉ A ∧ a ∉ GFV t ⇒ a ∉ supp dpm r``,
  strip_tac >> Induct_on `recn_rel` >> srw_tac [][NOT_IN_GFV] >|[
    `support dpm (vf s vv) (A ∪ {s})`
       by (srw_tac [][support_def] >>
           `lswapstr [(x,y)] s = s` by srw_tac [][] >>
           metis_tac []) >>
    match_mp_tac sub_cpos >> qexists_tac `A ∪ {s}` >>
    srw_tac [][supp_smallest],

    `v ∉ supp dpm (lf v bv ds1 ts ds2 us)` by metis_tac [] >>
    Cases_on `a = v` >- srw_tac [][] >> strip_tac >>
    `FINITE (supp dpm (lf v bv ds1 ts ds2 us))`
       by metis_tac [supp_absence_FINITE] >>
    Q_TAC (NEW_TAC "b") `A ∪ supp dpm (lf v bv ds1 ts ds2 us) ∪ {v} ∪
                         supp (listpm gtpm) ts ∪ supp (listpm gtpm) us` >>
    `dpm [(a,b)] (lf v bv ds1 ts ds2 us) ≠ lf v bv ds1 ts ds2 us`
       by metis_tac [supp_apart] >>
    pop_assum mp_tac >> srw_tac [][] >>
    first_x_assum (qspecl_then [`a`,`b`, `n`, `v`, `bv`, `ds1`, `ts`,
                                `ds2`, `us`, `ns`, `ms`] mp_tac) >>
    `a ∉ supp (listpm gtpm) ts ∧ a ∉ supp (listpm gtpm) us`
      by srw_tac [][NOT_IN_supp_listpm, GFV_supp] >>
    srw_tac [][supp_fresh] >>
    fsrw_tac [][list_rel_split] >>
    qsuff_tac `a ∉ supp (listpm dpm) ds1 ∧ b ∉ supp (listpm dpm) ds1 ∧
               a ∉ supp (listpm dpm) ds2 ∧ b ∉ supp (listpm dpm) ds2`
    >- srw_tac [][supp_fresh] >>
    fsrw_tac [DNF_ss][LIST_REL_EL_EQN, MEM_EL, NOT_IN_supp_listpm,
                      GSYM GFV_supp]
  ]);

val list_rel_eqv0 = prove(
  ``^permsupp_sidecond ∧ v ∉ A ∧ v' ∉ A ==>
    ∀ts ds. LIST_REL ^recnrel ts ds ==>
            LIST_REL ^recnrel
                     (listpm gtpm [(v,v')] ts)
                     (listpm dpm [(v,v')] ds)``,
  strip_tac >> Induct_on `LIST_REL` >> srw_tac [][] >>
  match_mp_tac (MP_CANON (GEN_ALL recn_rel_equivariant)) >>
  metis_tac []);

val list_rel_eqv = prove(
  ``^permsupp_sidecond ∧ v ∉ A ∧ v' ∉ A ⇒
    (LIST_REL ^recnrel (listpm gtpm [(v,v')] ts) ds ⇔
     LIST_REL ^recnrel ts (listpm dpm [(v,v')] ds))``,
  DISCH_THEN (fn th => ASSUME_TAC (MP list_rel_eqv0 th) >>
                       ASSUME_TAC (hd (CONJUNCTS th))) >>
  srw_tac [][EQ_IMP_THM] >>
  first_x_assum (fn impth => first_x_assum (MP_TAC o MATCH_MP impth)) >>
  srw_tac [ETA_ss][is_perm_sing_inv, is_perm_nil]);

val list_rel_freshness = prove(
  ``^permsupp_sidecond ∧ ^FCB ⇒
    ∀ts ds. LIST_REL ^recnrel ts ds ⇒
            ∀a. a ∉ supp (listpm gtpm) ts ∧ a ∉ A ⇒
                a ∉ supp (listpm dpm) ds``,
  DISCH_THEN (ASSUME_TAC o MP freshness) >>
  Induct_on `LIST_REL` >> srw_tac [][] >>
  metis_tac [GFV_supp]);

val list_rel_eqv' =
    list_rel_eqv |> REWRITE_RULE [ASSUME ``v:string ∉ A ∧ v' ∉ A``]
                 |> UNDISCH
                 |> Q.GEN `ds` |> Q.GEN `ts`
                 |> DISCH ``v:string ∉ A ∧ v' ∉ A``
                 |> Q.GEN `v'` |> Q.GEN `v`
                 |> DISCH_ALL

(* UB lemma 8 *)
val uniqueness = prove(
  ``^permsupp_sidecond ∧ ^FCB ==>
    ∀t r. ^recnrel t r ⇒ ∀r'. ^recnrel t r' ==> (r' = r)``,
  DISCH_THEN (fn th => ASSUME_TAC (MP list_rel_freshness th) >>
                       ASSUME_TAC (MP list_rel_eqv' (CONJUNCT1 th)) >>
                       STRIP_ASSUME_TAC th) >>
  Induct_on `recn_rel` >>
  srw_tac [ETA_ss][list_rel_split, MAP_gtpm]
  >- ((* var case *) qpat_assum `recn_rel X Y Z A1 A2 U U'` MP_TAC >>
      srw_tac [][Once recn_rel_cases, gterm_distinct, gterm_11]) >>

  (* lam case *)
  qpat_assum `recn_rel X Y Z A1 A2 U U'` MP_TAC >>
  srw_tac[] [Once recn_rel_cases, gterm_distinct, gterm_11] >>
  `us' = us` by fsrw_tac [][GLAM_eq_thm] >> srw_tac [][] >>
  `ds2' = ds2`
     by (rpt (qpat_assum `LIST_REL R us Y` MP_TAC) >>
         rpt (pop_assum (K ALL_TAC)) >>
         map_every qid_spec_tac [`ds2`, `ds2'`] >> Induct_on `us` >>
         Cases_on `ds2` >> srw_tac [][] >>
         Cases_on `ds2'` >> fsrw_tac [][]) >>
  srw_tac [][] >> Cases_on `v = v'`
  >- (srw_tac [][] >> fsrw_tac [][GLAM_eq_thm] >> srw_tac [][] >>
      qsuff_tac `ds1' = ds1` >- srw_tac [][] >>
      rpt (qpat_assum `LIST_REL R ts Y` MP_TAC) >>
      rpt (pop_assum (K ALL_TAC)) >>
      map_every qid_spec_tac [`ds1`, `ds1'`] >> Induct_on `ts` >>
      Cases_on `ds1` >> srw_tac [][] >>
      Cases_on `ds1'` >> fsrw_tac [][]) >>

  (* hard case, bvars not equal *)
  qpat_assum `GLAM X X' Y Y' = GLAM A1 A2 A3 A4` MP_TAC >>
  asm_simp_tac (srw_ss()) [REWRITE_RULE [gfvl_supp] GLAM_eq_thm,
                           MAP_gtpm] >>
  full_simp_tac (srw_ss() ++ ETA_ss) [] >> rpt strip_tac >>
  `LIST_REL ^recnrel ts (listpm dpm [(v,v')] ds1')`
     by srw_tac [ETA_ss][is_perm_nil] >>
  `ds1 = listpm dpm [(v,v')] ds1'`
     by (rpt (qpat_assum `LIST_REL R ts Y` MP_TAC) >>
         rpt (pop_assum (K ALL_TAC)) >>
         map_every qid_spec_tac [`ds1`, `ds1'`] >> Induct_on `ts` >>
         Cases_on `ds1` >> srw_tac [][] >>
         Cases_on `ds1'` >> fsrw_tac [][]) >>
  pop_assum SUBST_ALL_TAC >>
  `v ∉ supp (listpm dpm) ds1'` by metis_tac [] >>
  `v ∉ supp (listpm dpm) ds2 ∧ v' ∉ supp (listpm dpm) ds2`
    by metis_tac [] >>
  `v' ∉ supp dpm (lf v' bv' ds1' ts' ds2 us)` by metis_tac [] >>
  `FINITE (supp (listpm dpm) ds1') ∧ FINITE (supp (listpm dpm) ds2) `
    by (CONJ_TAC >> match_mp_tac (GEN_ALL supp_absence_FINITE)  >>
        qexists_tac `v` >> srw_tac [][]) >>
  `FINITE (supp dpm (lf v' bv' ds1' ts' ds2 us))`
     by (match_mp_tac (GEN_ALL supp_absence_FINITE) >> qexists_tac `v'` >>
         srw_tac [][]) >>
  `v ∉ supp dpm (lf v' bv' ds1' ts' ds2 us)`
    by (strip_tac >> srw_tac [][] >>
        Q_TAC (NEW_TAC "z")
           `supp dpm (lf v' bv ds1' ts' ds2 us) ∪ A ∪ {v';v} ∪
            supp (listpm gtpm) ts' ∪ supp (listpm gtpm) us ∪
            supp (listpm dpm) ds1' ∪supp (listpm dpm) ds2` >>
        `dpm [(v,z)] (lf v' bv ds1' ts' ds2 us) ≠ lf v' bv ds1' ts' ds2 us`
           by metis_tac [supp_apart] >>
        pop_assum mp_tac >> srw_tac [][] >>
        first_x_assum (qspecl_then [`v`, `z`, `n`, `v'`, `bv`, `ds1'`, `ts'`,
                                    `ds2`, `us`, `ns`, `ms`] mp_tac) >>
        fsrw_tac [][LIST_REL_genind_gtpm_eqn] >> DISCH_THEN (K ALL_TAC) >>
        srw_tac [][supp_fresh]) >>
  `ds2 = listpm dpm [(v,v')] ds2` by srw_tac [][supp_fresh] >>
  POP_ASSUM (fn th => simp_tac (srw_ss()) [Once th, SimpRHS]) >>
  `us = listpm gtpm [(v,v')] us` by srw_tac [][supp_fresh] >>
  POP_ASSUM (fn th => simp_tac (srw_ss()) [Once th, SimpRHS]) >>
  `lf v = lf (lswapstr [(v,v')] v')` by srw_tac [][] >>
  POP_ASSUM SUBST1_TAC >>
  first_x_assum (qspecl_then [`v`, `v'`, `n`, `v'`, `bv`, `ds1'`, `ts'`,
                              `ds2`, `us`, `ns`, `ms`] (MP_TAC o GSYM)) >>
  fsrw_tac [][LIST_REL_genind_gtpm_eqn] >> DISCH_THEN (K ALL_TAC) >>
  srw_tac [][supp_fresh]);

val listrel_uniqueness1 = prove(
  ``^permsupp_sidecond ∧ ^FCB ⇒
    ∀ts ds. LIST_REL ^recnrel ts ds ⇒
            (MAP (λt. @r. ^recnrel t r) ts = ds)``,
  DISCH_THEN (ASSUME_TAC o MP uniqueness) >>
  Induct_on `LIST_REL` >> srw_tac [][] >>
  `∀r. ^recnrel h1 r ⇔ (r = h2)` by metis_tac [] >>
  srw_tac [][]);
val listrel_uniqueness2 = prove(
  ``^permsupp_sidecond ∧ ^FCB ⇒
    ∀ts ds. LIST_REL ^recnrel ts ds ⇒
            ∀ds'. LIST_REL ^recnrel ts ds' ⇔ (ds' = ds)``,
  DISCH_THEN (ASSUME_TAC o MP uniqueness) >>
  Induct_on `LIST_REL` >> srw_tac [][] >>
  Cases_on `ds'` >> srw_tac [][] >> metis_tac []);

val recursion_axiom = store_thm(
  "recursion_axiom",
  ``^permsupp_sidecond ∧ ^FCB ⇒
    ∃h. (∀s vv n. vp n vv ⇒ (h (GVAR s vv) = vf s vv)) ∧
        (∀bv v ts us ns ms.
            v ∉ A ∧ v ∉ supp (listpm gtpm) us ∧
            LIST_REL (genind vp lp) ns ts ∧
            LIST_REL (genind vp lp) ms us ∧ lp n bv ns ms ⇒
            (h (GLAM v bv ts us) = lf v bv (MAP h ts) ts (MAP h us) us))``,
  DISCH_THEN (fn th => ASSUME_TAC (MP uniqueness th) >>
                       ASSUME_TAC (MP listrel_uniqueness1 th) >>
                       STRIP_ASSUME_TAC th)>>
  qexists_tac `λt. @r. ^recnrel t r` >> srw_tac [][] >|[
    ONCE_REWRITE_TAC [recn_rel_cases] >>
    srw_tac [][gterm_11, gterm_distinct] >>
    srw_tac [SatisfySimps.SATISFY_ss][RIGHT_EXISTS_AND_THM],

    `(∃ds. LIST_REL ^recnrel ts ds) ∧ (∃es.  LIST_REL ^recnrel us es)`
        by (srw_tac [][LIST_REL_exists] >>
            fsrw_tac [][LIST_REL_EL_EQN, MEM_EL] >>
            metis_tac [recn_rel_exists]) >>
    `MAP (λt. @r. ^recnrel t r) ts = ds`
      by (first_x_assum match_mp_tac >> srw_tac [][]) >>
    `MAP (λt. @r. ^recnrel t r) us = es`
      by (first_x_assum match_mp_tac >> srw_tac [][]) >>
    `^recnrel (GLAM v bv ts us) (lf v bv ds ts es us)`
      by (match_mp_tac rlam >> metis_tac []) >>
    `∀r. ^recnrel (GLAM v bv ts us) r ⇔ (r = lf v bv ds ts es us)`
      by metis_tac [] >>
    srw_tac [][]
  ]);

val _ = export_theory()



