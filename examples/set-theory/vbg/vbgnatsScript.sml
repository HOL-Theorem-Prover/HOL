open HolKernel Parse boolLib bossLib
open vbgsetTheory
open boolSimps

val _ = new_theory "vbgnats"

val vSUC_def = Define`vSUC x = x ∪ {x}`

val fromNat_def = Define`
  (fromNat 0 = {}) ∧
  (fromNat (SUC n) = vSUC (fromNat n))
`;
val _ = add_numeral_form(#"v", SOME "fromNat")

val inductive_def = Define`
  inductive A ⇔ SET A ∧ {} ∈ A ∧ ∀x. x ∈ A ⇒ vSUC x ∈ A
`;

val Inductives_def = Define`
  Inductives = SPEC0 (λA. {} ∈ A ∧ ∀x. x ∈ A ⇒ vSUC x ∈ A)
`;

val inductive_Inductives = store_thm(
  "inductive_Inductives",
  ``inductive A ⇔ A ∈ Inductives``,
  srw_tac [][inductive_def, Inductives_def, SPEC0]);

val Nats_def = Define`
  Nats = SPEC0 (λn. ∀s. inductive s ⇒ n ∈ s)
`;

val EMPTY_IN_Nats = store_thm(
  "EMPTY_IN_Nats",
  ``{} ∈ Nats``,
  rw [Nats_def, SPEC0, inductive_def]);

val vSUC_IN_Nats_I = store_thm(
  "vSUC_IN_Nats_I",
  ``n ∈ Nats ⇒ vSUC n ∈ Nats``,
  rw [Nats_def, SPEC0, inductive_def, vSUC_def]);

val SET_fromNat = store_thm(
  "SET_fromNat",
  ``SET (fromNat n)``,
  Induct_on `n` >> srw_tac [][fromNat_def, vSUC_def]);
val _ = export_rewrites ["SET_fromNat"]

val fromNat_in_Nats = store_thm(
  "fromNat_in_Nats",
  ``∀n. fromNat n ∈ Nats``,
  Induct THEN SRW_TAC [][fromNat_def] THENL [
    SRW_TAC [][Nats_def, SPEC0] THEN
    fs [inductive_def],
    fs [Nats_def, SPEC0, vSUC_def] >>
    fs [inductive_def, vSUC_def]
  ]);
val _ = export_rewrites ["fromNat_in_Nats"]

val NOT_IN_0 = store_thm(
  "NOT_IN_0",
  ``x ∉ 0``,
  SRW_TAC [][fromNat_def]);
val _ = export_rewrites ["NOT_IN_0"]

val vSUC_NOT_0 = store_thm(
  "vSUC_NOT_0",
  ``vSUC n ≠ 0``,
  SRW_TAC [][vSUC_def, EXTENSION] THEN
  Cases_on `n = 0` THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `0` THEN SRW_TAC [][],
    METIS_TAC [fromNat_def, EMPTY_UNIQUE]
  ]);
val _ = export_rewrites ["vSUC_NOT_0"]

val Nats_SET = store_thm(
  "Nats_SET",
  ``SET Nats``,
  match_mp_tac SUBSETS_ARE_SETS >>
  strip_assume_tac INFINITY >>
  qexists_tac `w` >> simp [SUBSET_def] >>
  qx_gen_tac `n` >> rw [Nats_def] >>
  first_assum match_mp_tac >> simp [inductive_def] >> conj_tac
    >- metis_tac [EMPTY_UNIQUE] >>
  qx_gen_tac `e` >> strip_tac >>
  `∃y. y ∈ w ∧ ∀u. u ∈ y ⇔ u ∈ e ∨ (u = e)` by metis_tac[] >>
  qsuff_tac `vSUC e = y` >- rw[] >>
  rw [vSUC_def, Once EXTENSION] >> metis_tac [SET_def]);

val Nats_inductive = store_thm(
  "Nats_inductive",
  ``Nats ∈ Inductives``,
  rw [SPEC0, SUBSET_def, Inductives_def, Nats_SET, EMPTY_IN_Nats,
      vSUC_IN_Nats_I]);

val Nats_least_inductive = store_thm(
  "Nats_least_inductive",
  ``P ∈ Inductives ⇒ Nats ⊆ P``,
  rw[Inductives_def, SUBSET_def] >>
  fs [Nats_def, inductive_def])

val Nats_SETs = prove(``n ∈ Nats ⇒ SET n``, metis_tac [SET_def])
val _ = augment_srw_ss [rewrites [Nats_SETs]]
(*
Higher order logic wins here: can capture all possible predicates.
Can simplify to membership of a set S by making the predicate P be just that.
 ⊢ ∀P. P 0 ∧ (∀x. P x ∧ x ∈ Nats ⇒ P (vSUC x)) ⇒ ∀u. u ∈ Nats ⇒ P u
*)
val nat_induction = save_thm(
  "nat_induction",
  Nats_least_inductive
      |> SIMP_RULE(srw_ss())[SUBSET_def,Inductives_def,SPEC0]
      |> Q.GEN `P`
      |> Q.SPEC `SPEC0 P ∩ Nats`
      |> SIMP_RULE (srw_ss() ++ CONJ_ss)
                   [Nats_SET, EMPTY_IN_Nats, vSUC_IN_Nats_I,
                    GSYM fromNat_def]
      |> Q.GEN `P`);
val _ = IndDefLib.export_rule_induction "nat_induction"

val transitive_def = Define`
  transitive X ⇔ ∀x. x ∈ X ⇒ x ⊆ X
`;

val transitive_ALT = store_thm(
  "transitive_ALT",
  ``transitive X ⇔ ∀x y. x ∈ y ∧ y ∈ X ⇒ x ∈ X``,
  rw [transitive_def] >> metis_tac [SUBSET_def]);

val Nats_transitive = store_thm(
  "Nats_transitive",
  ``∀n. n ∈ Nats ⇒ transitive n``,
  ho_match_mp_tac nat_induction >> conj_tac >> rw[transitive_def] >>
  fs [vSUC_def, SUBSET_def] >> metis_tac []);

(* pointless given axiom of foundation - in its absence, this proof works
val Nats_not_selfmembers = store_thm(
  "Nats_not_selfmembers",
  ``∀n. n ∈ Nats ⇒ n ∉ n``,
  ho_match_mp_tac nat_induction >> rw[vSUC_def] >| [
    strip_tac >> `n ∈ n ∪ {n}` by rw[] >>
    metis_tac [Nats_transitive, transitive_ALT],
    rw[Once EXTENSION] >> metis_tac []
  ]);
*)

val pre_IN_vSUC = store_thm(
  "pre_IN_vSUC",
  ``SET n ⇒ n ∈ vSUC n``,
  rw[vSUC_def]);

val SET_vSUC = store_thm(
  "SET_vSUC",
  ``SET (vSUC n) = SET n``,
  rw[vSUC_def, EQ_IMP_THM]);
val _ = export_rewrites ["SET_vSUC"]

(* doing this the longwinded way, with appeals to foundation all over the
   place gives a stronger rewrite rule without requiring n and m to be ∈ Nats *)
val vSUC_11 = store_thm(
  "vSUC_11",
  ``∀n m. ((vSUC n = vSUC m) ⇔ (n = m))``,
  rw[EQ_IMP_THM] >> Cases_on `SET n` >| [
    fs[vSUC_def] >> rw[EXTENSION] >>
    `SET m` by metis_tac [UNION_SET_CLOSED, SET_INSERT, EMPTY_SET] >>
    first_assum (qspec_then `x` mp_tac o
                 SIMP_RULE (srw_ss()) [Once EXTENSION]) >>
    simp[] >>
    Cases_on `x ∈ n` >> simp[] >| [
      rw[DISJ_IMP_THM] >> strip_tac >> rw[] >>
      first_assum (qspec_then `n` mp_tac o
                   SIMP_RULE (srw_ss()) [Once EXTENSION]) >>
      rw[] >> metis_tac [IN_ANTISYM, IN_REFL],
      Cases_on `x = n` >> simp[DISJ_IMP_THM] >> strip_tac >> rw[] >>
      first_assum (qspec_then `m` mp_tac o
                   SIMP_RULE (srw_ss()) [Once EXTENSION]) >>
      rw[] >> metis_tac [IN_ANTISYM, IN_REFL]
    ],

    fs[vSUC_def] >>
    `¬SET m` by metis_tac [UNION_SET_CLOSED, SET_INSERT, EMPTY_SET] >>
    `({n} = {}) ∧ ({m} = {})`
       by metis_tac [INSERT_def, PCLASS_SINGC_EMPTY, EMPTY_UNION] >>
    fs[]
  ]);
val _ = export_rewrites ["vSUC_11"]

val Nats_CASES = store_thm(
  "Nats_CASES",
  ``∀n. n ∈ Nats ⇔ (n = 0) ∨ ∃m. m ∈ Nats ∧ (n = vSUC m)``,
  simp_tac (srw_ss() ++ DNF_ss)[EQ_IMP_THM, vSUC_IN_Nats_I] >>
  Induct_on `n ∈ Nats` >> metis_tac []);

val vSUC_IN_NATS = store_thm(
  "vSUC_IN_NATS",
  ``∀n. vSUC n ∈ Nats ⇔ n ∈ Nats``,
  simp[EQ_IMP_THM, vSUC_IN_Nats_I] >>
  qsuff_tac `∀m. m ∈ Nats ⇒ ∀n. (m = vSUC n) ⇒ n ∈ Nats` >- metis_tac [] >>
  Induct_on `m ∈ Nats` >> simp[]);
val _ = export_rewrites ["vSUC_IN_NATS"]

(* less than or equal *)
val nle_def = Define`
  nle = SPEC0 (λp. ∀P. (∀x. x ∈ Nats ⇒ 〈0·x〉 ∈ P) ∧
                       (∀x y. x ∈ Nats ∧ y ∈ Nats ∧ 〈x·y〉 ∈ P ⇒
                              〈vSUC x·vSUC y〉 ∈ P) ⇒
                       p ∈ P)
`;

val _ = overload_on ("<=", ``λx y. 〈x·y〉 ∈ nle``)
val _ = overload_on ("<", ``λx:vbgc y. ¬ (y ≤ x)``)

val ZERO_LE = store_thm(
  "ZERO_LE",
  ``∀n. n ∈ Nats ⇒ 0 ≤ n``,
  rw [nle_def]);
val _ = export_rewrites ["ZERO_LE"]

val nle_Nats = store_thm(
  "nle_Nats",
  ``n ≤ m ⇒ n ∈ Nats ∧ m ∈ Nats``,
  rw[nle_def] >> pop_assum (qspec_then `Nats × Nats` mp_tac) >>
  asm_simp_tac (srw_ss() ++ CONJ_ss)[CROSS_def]);

val nle_induct = store_thm(
  "nle_induct",
  ``(∀n. n ∈ Nats ⇒ P 0 n) ∧
    (∀n m. n ∈ Nats ∧ m ∈ Nats ∧ P n m ⇒ P (vSUC n) (vSUC m)) ⇒
    ∀n m. n ≤ m ⇒ P n m``,
  rw[nle_def] >>
  qsuff_tac `〈n·m〉 ∈ SPEC0 (λp. ∃x y. (p = 〈x·y〉) ∧ P x y)` >-
    simp_tac (srw_ss()) [] >>
  pop_assum match_mp_tac >> simp[]);
val _ = IndDefLib.export_rule_induction "nle_induct"

val vSUC_LE_I = store_thm(
  "vSUC_LE_I",
  ``n ≤ m ⇒ vSUC n ≤ vSUC m``,
  strip_tac >> imp_res_tac nle_Nats >>
  fs[nle_def]);

val LE_CASES = store_thm(
  "LE_CASES",
  ``n ≤ m ⇔ (n = 0) ∧ m ∈ Nats ∨
            ∃n0 m0. n0 ∈ Nats ∧ m0 ∈ Nats ∧ (n = vSUC n0) ∧
                    (m = vSUC m0) ∧ n0 ≤ m0``,
  Tactical.REVERSE EQ_TAC >- (rw[] >> rw[vSUC_LE_I]) >>
  map_every qid_spec_tac [`m`, `n`] >> ho_match_mp_tac nle_induct >>
  srw_tac [CONJ_ss][vSUC_LE_I] >> rw[vSUC_LE_I]);

val vSUC_LE1 = store_thm(
  "vSUC_LE1",
  ``vSUC n ≤ vSUC m ⇔ n ≤ m``,
  eq_tac >-
     (asm_simp_tac (srw_ss() ++ CONJ_ss)
                   [SimpL ``(==>)``, Once LE_CASES] >> rw[]) >>
  rw[vSUC_LE_I]);
val _ = export_rewrites ["vSUC_LE1"]

val vSUC_ZERO_LE = store_thm(
  "vSUC_ZERO_LE",
  ``¬ (vSUC n ≤ 0)``,
  rw[Once LE_CASES]);
val _ = export_rewrites ["vSUC_ZERO_LE"]

val LE_REFL0 = prove(
  ``∀n. n ∈ Nats ⇒ n ≤ n``,
  ho_match_mp_tac nat_induction >> rw[vSUC_LE_I])

val LE_REFL = store_thm(
  "LE_REFL",
  ``n ≤ n ⇔ n ∈ Nats``,
  metis_tac [nle_Nats, LE_REFL0]);
val _ = export_rewrites ["LE_REFL"]

val LE_ANTISYM0 = prove(
  ``∀n m. n ≤ m ⇒ m ≤ n ⇒ (m = n)``,
  ho_match_mp_tac nle_induct >> simp[vSUC_LE1] >>
  rw[Once LE_CASES]);

val LE_ANTISYM = store_thm(
  "LE_ANTISYM",
  ``∀n m. n ≤ m ∧ m ≤ n ⇒ (m = n)``,
  metis_tac [LE_ANTISYM0]);

val LE_TRANS = store_thm(
  "LE_TRANS",
  ``∀x y z. x ≤ y ∧ y ≤ z ⇒ x ≤ z``,
  qsuff_tac `∀x y. x ≤ y ⇒ ∀z. y ≤ z ⇒ x ≤ z` >- metis_tac [] >>
  ho_match_mp_tac nle_induct >> rw[] >|[
    `z ∈ Nats` by metis_tac [nle_Nats] >> rw[],
    pop_assum mp_tac >>
    asm_simp_tac (srw_ss() ++ CONJ_ss) [SimpL ``(==>)``, Once LE_CASES] >>
    asm_simp_tac (srw_ss() ++ DNF_ss)[]
  ]);

val LE_TOTAL = store_thm(
  "LE_TOTAL",
  ``∀n m. n ∈ Nats ∧ m ∈ Nats ⇒ n ≤ m ∨ m ≤ n``,
  qsuff_tac `∀n. n ∈ Nats ⇒ ∀m. m ∈ Nats ⇒ n ≤ m ∨ m ≤ n` >- metis_tac[] >>
  ho_match_mp_tac nat_induction >> rw[] >>
  qspec_then `m` mp_tac Nats_CASES >> rw[] >> rw[]);


val LESS_ZERO = store_thm(
  "LESS_ZERO",
  ``m ≤ 0 ⇔ (m = 0)``,
  rw[Once LE_CASES]);
val _ = export_rewrites ["LESS_ZERO"]

val LE_LT_EQ0 = prove(
  ``∀m n. m ≤ n ⇒ m < n ∨ (m = n)``,
  Induct_on `m ≤ n` >> rw[] >> metis_tac []);

(* DON'T USE THIS AS A REWRITE!

   It loops because the m < n on the right is really just ~(n <= m) *)
val LE_LT_EQ = store_thm(
  "LE_LT_EQ",
  ``∀m n. m ≤ n ⇔ m ∈ Nats ∧ n ∈ Nats ∧ (m < n ∨ (m = n))``,
  metis_tac [LE_LT_EQ0, LE_REFL, LE_TOTAL, nle_Nats]);

val LE_DISCRETE = store_thm(
  "LE_DISCRETE",
  ``∀m n. m ∈ Nats ∧ n ∈ Nats ⇒ m ≤ n ∨ vSUC n ≤ m``,
  qsuff_tac `∀m. m ∈ Nats ⇒ ∀n. n ∈ Nats ⇒ m ≤ n ∨ vSUC n ≤ m` >- metis_tac[]>>
  Induct_on `m ∈ Nats` >> rw[] >> qspec_then `n` mp_tac Nats_CASES >>
  asm_simp_tac (srw_ss() ++ DNF_ss)[DISJ_IMP_THM]);

val complete_induction = store_thm(
  "complete_induction",
  ``∀P.
      (∀n. (∀m. m ∈ Nats ∧ m < n ⇒ P m) ⇒ P n) ⇒ ∀n. n ∈ Nats ⇒ P n``,
  gen_tac >> strip_tac >>
  qsuff_tac `∀n. n ∈ Nats ⇒ ∀m. m ≤ n ⇒ P m`
    >- metis_tac [LE_REFL] >>
  Induct_on `n ∈ Nats` >> srw_tac [CONJ_ss][] >>
  Cases_on `m ≤ n` >- metis_tac [] >>
  `m = vSUC n` by metis_tac [LE_DISCRETE, LE_LT_EQ] >> rw[] >>
  metis_tac [LE_DISCRETE]);

val rwt = SUBSET_def |> Q.SPECL [`B`, `Nats`] |> EQ_IMP_RULE |> #1 |> UNDISCH

(* ⊢ B ⊆ Nats ∧ (∃n. n ∈ B) ⇒ ∃n. n ∈ B ∧ ∀m. m ∈ B ⇒ n ≤ m *)
val Nats_least_element = save_thm(
  "Nats_least_element",
  complete_induction |> Q.SPEC `λn. n ∉ B`
                     |> CONV_RULE CONTRAPOS_CONV
                     |> SIMP_RULE bool_ss []
                     |> CONV_RULE
                          (RAND_CONV (ONCE_DEPTH_CONV CONTRAPOS_CONV))
                     |> SIMP_RULE (srw_ss() ++ CONJ_ss) [rwt]
                     |> SIMP_RULE bool_ss [Once CONJ_COMM]
                     |> DISCH_ALL
                     |> REWRITE_RULE [AND_IMP_INTRO]);



val _ = export_theory()
