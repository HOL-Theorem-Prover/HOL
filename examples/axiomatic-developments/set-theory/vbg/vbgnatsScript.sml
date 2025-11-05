Theory vbgnats
Ancestors
  vbgset
Libs
  boolSimps

Definition vSUC_def:  vSUC x = x ∪ {x}
End

Definition fromNat_def:
  (fromNat 0 = {}) ∧
  (fromNat (SUC n) = vSUC (fromNat n))
End
val _ = add_numeral_form(#"v", SOME "fromNat")

Definition inductive_def:
  inductive A ⇔ SET A ∧ {} ∈ A ∧ ∀x. x ∈ A ⇒ vSUC x ∈ A
End

Definition Inductives_def:
  Inductives = SPEC0 (λA. {} ∈ A ∧ ∀x. x ∈ A ⇒ vSUC x ∈ A)
End

Theorem inductive_Inductives:
    inductive A ⇔ A ∈ Inductives
Proof
  srw_tac [][inductive_def, Inductives_def, SPEC0]
QED

Definition Nats_def:
  Nats = SPEC0 (λn. ∀s. inductive s ⇒ n ∈ s)
End

Theorem EMPTY_IN_Nats:
    {} ∈ Nats
Proof
  rw [Nats_def, SPEC0, inductive_def]
QED

Theorem vSUC_IN_Nats_I:
    n ∈ Nats ⇒ vSUC n ∈ Nats
Proof
  rw [Nats_def, SPEC0, inductive_def, vSUC_def]
QED

Theorem SET_fromNat:
    SET (fromNat n)
Proof
  Induct_on `n` >> srw_tac [][fromNat_def, vSUC_def]
QED
val _ = export_rewrites ["SET_fromNat"]

Theorem fromNat_in_Nats:
    ∀n. fromNat n ∈ Nats
Proof
  Induct THEN SRW_TAC [][fromNat_def] THENL [
    SRW_TAC [][Nats_def, SPEC0] THEN
    fs [inductive_def],
    fs [Nats_def, SPEC0, vSUC_def] >>
    fs [inductive_def, vSUC_def]
  ]
QED
val _ = export_rewrites ["fromNat_in_Nats"]

Theorem NOT_IN_0:
    x ∉ 0
Proof
  SRW_TAC [][fromNat_def]
QED
val _ = export_rewrites ["NOT_IN_0"]

Theorem vSUC_NOT_0:
    vSUC n ≠ 0
Proof
  SRW_TAC [][vSUC_def, EXTENSION] THEN
  Cases_on `n = 0` THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `0` THEN SRW_TAC [][],
    METIS_TAC [fromNat_def, EMPTY_UNIQUE]
  ]
QED
val _ = export_rewrites ["vSUC_NOT_0"]

Theorem Nats_SET:
    SET Nats
Proof
  match_mp_tac SUBSETS_ARE_SETS >>
  strip_assume_tac INFINITY >>
  qexists_tac `w` >> simp [SUBSET_def] >>
  qx_gen_tac `n` >> rw [Nats_def] >>
  first_assum match_mp_tac >> simp [inductive_def] >> conj_tac
    >- metis_tac [EMPTY_UNIQUE] >>
  qx_gen_tac `e` >> strip_tac >>
  `∃y. y ∈ w ∧ ∀u. u ∈ y ⇔ u ∈ e ∨ (u = e)` by metis_tac[] >>
  qsuff_tac `vSUC e = y` >- rw[] >>
  rw [vSUC_def, Once EXTENSION] >> metis_tac [SET_def]
QED

Theorem Nats_inductive:
    Nats ∈ Inductives
Proof
  rw [SPEC0, SUBSET_def, Inductives_def, Nats_SET, EMPTY_IN_Nats,
      vSUC_IN_Nats_I]
QED

Theorem Nats_least_inductive:
    P ∈ Inductives ⇒ Nats ⊆ P
Proof
  rw[Inductives_def, SUBSET_def] >>
  fs [Nats_def, inductive_def]
QED

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

Definition transitive_def:
  transitive X ⇔ ∀x. x ∈ X ⇒ x ⊆ X
End

Theorem transitive_ALT:
    transitive X ⇔ ∀x y. x ∈ y ∧ y ∈ X ⇒ x ∈ X
Proof
  rw [transitive_def] >> metis_tac [SUBSET_def]
QED

Theorem Nats_transitive:
    ∀n. n ∈ Nats ⇒ transitive n
Proof
  ho_match_mp_tac nat_induction >> conj_tac >> rw[transitive_def] >>
  fs [vSUC_def, SUBSET_def] >> metis_tac []
QED

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

Theorem pre_IN_vSUC:
    SET n ⇒ n ∈ vSUC n
Proof
  rw[vSUC_def]
QED

Theorem SET_vSUC:
    SET (vSUC n) = SET n
Proof
  rw[vSUC_def, EQ_IMP_THM]
QED
val _ = export_rewrites ["SET_vSUC"]

(* doing this the longwinded way, with appeals to foundation all over the
   place gives a stronger rewrite rule without requiring n and m to be ∈ Nats *)
Theorem vSUC_11:
    ∀n m. ((vSUC n = vSUC m) ⇔ (n = m))
Proof
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
  ]
QED
val _ = export_rewrites ["vSUC_11"]

Theorem Nats_CASES:
    ∀n. n ∈ Nats ⇔ (n = 0) ∨ ∃m. m ∈ Nats ∧ (n = vSUC m)
Proof
  simp_tac (srw_ss() ++ DNF_ss)[EQ_IMP_THM, vSUC_IN_Nats_I] >>
  Induct_on `n ∈ Nats` >> metis_tac []
QED

Theorem vSUC_IN_NATS:
    ∀n. vSUC n ∈ Nats ⇔ n ∈ Nats
Proof
  simp[EQ_IMP_THM, vSUC_IN_Nats_I] >>
  qsuff_tac `∀m. m ∈ Nats ⇒ ∀n. (m = vSUC n) ⇒ n ∈ Nats` >- metis_tac [] >>
  Induct_on `m ∈ Nats` >> simp[]
QED
val _ = export_rewrites ["vSUC_IN_NATS"]

(* less than or equal *)
Definition nle_def:
  nle = SPEC0 (λp. ∀P. (∀x. x ∈ Nats ⇒ 〈0·x〉 ∈ P) ∧
                       (∀x y. x ∈ Nats ∧ y ∈ Nats ∧ 〈x·y〉 ∈ P ⇒
                              〈vSUC x·vSUC y〉 ∈ P) ⇒
                       p ∈ P)
End

val _ = overload_on ("<=", ``λx y. 〈x·y〉 ∈ nle``)
val _ = overload_on ("<", ``λx:vbgc y. ¬ (y ≤ x)``)

Theorem ZERO_LE:
    ∀n. n ∈ Nats ⇒ 0 ≤ n
Proof
  rw [nle_def]
QED
val _ = export_rewrites ["ZERO_LE"]

Theorem nle_Nats:
    n ≤ m ⇒ n ∈ Nats ∧ m ∈ Nats
Proof
  rw[nle_def] >> pop_assum (qspec_then `Nats × Nats` mp_tac) >>
  asm_simp_tac (srw_ss() ++ CONJ_ss)[CROSS_def]
QED

Theorem nle_induct:
    (∀n. n ∈ Nats ⇒ P 0 n) ∧
    (∀n m. n ∈ Nats ∧ m ∈ Nats ∧ P n m ⇒ P (vSUC n) (vSUC m)) ⇒
    ∀n m. n ≤ m ⇒ P n m
Proof
  rw[nle_def] >>
  qsuff_tac `〈n·m〉 ∈ SPEC0 (λp. ∃x y. (p = 〈x·y〉) ∧ P x y)` >-
    simp_tac (srw_ss()) [] >>
  pop_assum match_mp_tac >> simp[]
QED
val _ = IndDefLib.export_rule_induction "nle_induct"

Theorem vSUC_LE_I:
    n ≤ m ⇒ vSUC n ≤ vSUC m
Proof
  strip_tac >> imp_res_tac nle_Nats >>
  fs[nle_def]
QED

Theorem LE_CASES:
    n ≤ m ⇔ (n = 0) ∧ m ∈ Nats ∨
            ∃n0 m0. n0 ∈ Nats ∧ m0 ∈ Nats ∧ (n = vSUC n0) ∧
                    (m = vSUC m0) ∧ n0 ≤ m0
Proof
  Tactical.REVERSE EQ_TAC >- (rw[] >> rw[vSUC_LE_I]) >>
  map_every qid_spec_tac [`m`, `n`] >> ho_match_mp_tac nle_induct >>
  srw_tac [CONJ_ss][vSUC_LE_I] >> rw[vSUC_LE_I]
QED

Theorem vSUC_LE1:
    vSUC n ≤ vSUC m ⇔ n ≤ m
Proof
  eq_tac >-
     (asm_simp_tac (srw_ss() ++ CONJ_ss)
                   [SimpL ``(==>)``, Once LE_CASES] >> rw[]) >>
  rw[vSUC_LE_I]
QED
val _ = export_rewrites ["vSUC_LE1"]

Theorem vSUC_ZERO_LE:
    ¬ (vSUC n ≤ 0)
Proof
  rw[Once LE_CASES]
QED
val _ = export_rewrites ["vSUC_ZERO_LE"]

val LE_REFL0 = prove(
  ``∀n. n ∈ Nats ⇒ n ≤ n``,
  ho_match_mp_tac nat_induction >> rw[vSUC_LE_I])

Theorem LE_REFL:
    n ≤ n ⇔ n ∈ Nats
Proof
  metis_tac [nle_Nats, LE_REFL0]
QED
val _ = export_rewrites ["LE_REFL"]

val LE_ANTISYM0 = prove(
  ``∀n m. n ≤ m ⇒ m ≤ n ⇒ (m = n)``,
  ho_match_mp_tac nle_induct >> simp[vSUC_LE1] >>
  rw[Once LE_CASES]);

Theorem LE_ANTISYM:
    ∀n m. n ≤ m ∧ m ≤ n ⇒ (m = n)
Proof
  metis_tac [LE_ANTISYM0]
QED

Theorem LE_TRANS:
    ∀x y z. x ≤ y ∧ y ≤ z ⇒ x ≤ z
Proof
  qsuff_tac `∀x y. x ≤ y ⇒ ∀z. y ≤ z ⇒ x ≤ z` >- metis_tac [] >>
  ho_match_mp_tac nle_induct >> rw[] >|[
    `z ∈ Nats` by metis_tac [nle_Nats] >> rw[],
    pop_assum mp_tac >>
    asm_simp_tac (srw_ss() ++ CONJ_ss) [SimpL ``(==>)``, Once LE_CASES] >>
    asm_simp_tac (srw_ss() ++ DNF_ss)[]
  ]
QED

Theorem LE_TOTAL:
    ∀n m. n ∈ Nats ∧ m ∈ Nats ⇒ n ≤ m ∨ m ≤ n
Proof
  qsuff_tac `∀n. n ∈ Nats ⇒ ∀m. m ∈ Nats ⇒ n ≤ m ∨ m ≤ n` >- metis_tac[] >>
  ho_match_mp_tac nat_induction >> rw[] >>
  qspec_then `m` mp_tac Nats_CASES >> rw[] >> rw[]
QED


Theorem LESS_ZERO:
    m ≤ 0 ⇔ (m = 0)
Proof
  rw[Once LE_CASES]
QED
val _ = export_rewrites ["LESS_ZERO"]

val LE_LT_EQ0 = prove(
  ``∀m n. m ≤ n ⇒ m < n ∨ (m = n)``,
  Induct_on `m ≤ n` >> rw[] >> metis_tac []);

(* DON'T USE THIS AS A REWRITE!

   It loops because the m < n on the right is really just ~(n <= m) *)
Theorem LE_LT_EQ:
    ∀m n. m ≤ n ⇔ m ∈ Nats ∧ n ∈ Nats ∧ (m < n ∨ (m = n))
Proof
  metis_tac [LE_LT_EQ0, LE_REFL, LE_TOTAL, nle_Nats]
QED

Theorem LE_DISCRETE:
    ∀m n. m ∈ Nats ∧ n ∈ Nats ⇒ m ≤ n ∨ vSUC n ≤ m
Proof
  qsuff_tac `∀m. m ∈ Nats ⇒ ∀n. n ∈ Nats ⇒ m ≤ n ∨ vSUC n ≤ m` >- metis_tac[]>>
  Induct_on `m ∈ Nats` >> rw[] >> qspec_then `n` mp_tac Nats_CASES >>
  asm_simp_tac (srw_ss() ++ DNF_ss)[DISJ_IMP_THM]
QED

Theorem complete_induction:
    ∀P.
      (∀n. (∀m. m ∈ Nats ∧ m < n ⇒ P m) ⇒ P n) ⇒ ∀n. n ∈ Nats ⇒ P n
Proof
  gen_tac >> strip_tac >>
  qsuff_tac `∀n. n ∈ Nats ⇒ ∀m. m ≤ n ⇒ P m`
    >- metis_tac [LE_REFL] >>
  Induct_on `n ∈ Nats` >> srw_tac [CONJ_ss][] >>
  Cases_on `m ≤ n` >- metis_tac [] >>
  `m = vSUC n` by metis_tac [LE_DISCRETE, LE_LT_EQ] >> rw[] >>
  metis_tac [LE_DISCRETE]
QED

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



