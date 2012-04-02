open HolKernel boolLib bossLib Parse
open lcsymtacs
open boolSimps

val _ = new_theory "vbgset"

(* hide constants from the existing (typed) set theory *)
val _ = app (ignore o hide) ["UNION", "IN", "SUBSET", "EMPTY", "INSERT",
                             "CROSS", "INTER", "BIGINTER", "BIGUNION"]

(* create a new type (of VBG classes) *)
val _ = new_type("vbgc", 0)

(* with this call, the syntax with ∈ is enabled as well. *)
val _ = new_constant ("IN", ``:vbgc -> vbgc -> bool``)

(* similarly, this abbreviation also allows for ∉ *)
val _ = overload_on ("NOTIN", ``λx y. ~(x ∈ y)``)

val SET_def = Define` SET(x) = ∃w. x ∈ w `
val SUBSET_def = Define`x ⊆ y <=> ∀u. u ∈ x ⇒ u ∈ y`

val EXTENSION = new_axiom ("EXTENSION", ``(a = b) <=> (∀x. x ∈ a <=> x ∈ b)``)

val SPECIFICATION = new_axiom(
  "SPECIFICATION",
  ``∀(P : vbgc -> bool). ∃w. ∀x. x ∈ w <=> SET(x) ∧ P(x)``);

val SPEC0 = new_specification(
  "SPEC0",
  ["SPEC0"],
  CONV_RULE SKOLEM_CONV SPECIFICATION);

val EMPTY_def = Define`EMPTY = SPEC0 (λx. F)`

val NOT_IN_EMPTY = store_thm(
  "NOT_IN_EMPTY",
  ``x ∉ {}``,
  SRW_TAC [][EMPTY_def, SPEC0]);
val _ = export_rewrites ["NOT_IN_EMPTY"]

val EMPTY_UNIQUE = store_thm(
  "EMPTY_UNIQUE",
  ``(∀x. x ∉ u) ⇒ (u = {})``,
  SRW_TAC [][EXTENSION]);

val INFINITY = new_axiom(
  "INFINITY",
  ``∃w. SET w ∧ (∃u. u ∈ w ∧ ∀x. x ∉ u) ∧
        ∀x. x ∈ w ⇒ ∃y. y ∈ w ∧ ∀u. u ∈ y <=> u ∈ x ∨ (u = x)``);

val EMPTY_SET = store_thm(
  "EMPTY_SET",
  ``SET {}``,
  STRIP_ASSUME_TAC INFINITY THEN
  `u = {}` by SRW_TAC [][EMPTY_UNIQUE] THEN
  `SET u` by METIS_TAC [SET_def] THEN
  METIS_TAC []);
val _ = export_rewrites ["EMPTY_SET"]

val EMPTY_SUBSET = store_thm(
  "EMPTY_SUBSET",
  ``{} ⊆ A ∧ (A ⊆ {} <=> (A = {}))``,
  SRW_TAC [][SUBSET_def] THEN METIS_TAC [EMPTY_UNIQUE, NOT_IN_EMPTY]);
val _ = export_rewrites ["EMPTY_SUBSET"]

val SUBSET_REFL = store_thm(
  "SUBSET_REFL",
  ``A ⊆ A``,
  SRW_TAC [][SUBSET_def]);
val _ = export_rewrites ["SUBSET_REFL"]

val SUBSET_ANTISYM = store_thm(
  "SUBSET_ANTISYM",
  ``(x = y) <=> x ⊆ y ∧ y ⊆ x``,
  SRW_TAC [][EXTENSION, SUBSET_def] THEN METIS_TAC []);

val SUBSET_TRANS = store_thm(
  "SUBSET_TRANS",
  ``x ⊆ y ∧ y ⊆ z ⇒ x ⊆ z``,
  SRW_TAC [][SUBSET_def])

val Sets_def = Define`Sets = SPEC0 (λx. T)`

val SET_Sets = store_thm(
  "SET_Sets",
  ``x ∈ Sets <=> SET x``,
  SRW_TAC [][Sets_def, SPEC0]);

val SUBSET_Sets = store_thm(
  "SUBSET_Sets",
  ``x ⊆ Sets``,
  SRW_TAC [][SUBSET_def, SET_Sets, SET_def] THEN METIS_TAC []);

val RUS_def = Define`
  RUS = SPEC0 (\x. x ∉ x)
`;

(* gives result
     ⊢ RUS ∈ RUS ⇔ SET RUS ∧ RUS ∉ RUS
*)
val RUSlemma =
``RUS ∈ RUS``
    |> (SIMP_CONV (srw_ss()) [RUS_def, Once SPEC0] THENC
        SIMP_CONV (srw_ss()) [GSYM RUS_def])

val RUS_not_SET = store_thm(
  "RUS_not_SET",
  ``¬ SET RUS``,
  METIS_TAC [RUSlemma]);

val POW_def = Define`POW A = SPEC0 (λx. x ⊆ A)`
val IN_POW = store_thm(
  "IN_POW",
  ``x ∈ POW A ⇔ SET x ∧ x ⊆ A``,
  SRW_TAC [][POW_def, SPEC0]);
val _ = export_rewrites ["IN_POW"]

val POWERSET = new_axiom(
  "POWERSET",
  ``SET a ⇒ ∃w. SET w ∧ ∀x. x ⊆ a ⇒ x ∈ w``);

val SUBSETS_ARE_SETS = store_thm(
  "SUBSETS_ARE_SETS",
  ``∀A B. SET A ∧ B ⊆ A ⇒ SET B``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC POWERSET THEN
  `B ∈ w` by METIS_TAC [] THEN
  METIS_TAC [SET_def]);

val POW_SET_CLOSED = store_thm(
  "POW_SET_CLOSED",
  ``∀a. SET a ⇒ SET (POW a)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC POWERSET THEN
  MATCH_MP_TAC SUBSETS_ARE_SETS THEN
  Q.EXISTS_TAC `w` THEN SRW_TAC [][Once SUBSET_def]);


val SINGC_def = Define`
  SINGC a = SPEC0 (λx. x = a)
`


val PCLASS_SINGC_EMPTY = store_thm(
  "PCLASS_SINGC_EMPTY",
  ``¬SET a ⇒ (SINGC a = {})``,
  SRW_TAC [][SINGC_def, SPEC0, Once EXTENSION]);

val SET_IN_SINGC = store_thm(
  "SET_IN_SINGC",
  ``SET a ⇒ (x ∈ SINGC a ⇔ (x = a))``,
  SRW_TAC [CONJ_ss][SINGC_def, SPEC0]);

val SINGC_11 = store_thm(
  "SINGC_11",
  ``SET x ∧ SET y ⇒ ((SINGC x = SINGC y) = (x = y))``,
  SRW_TAC [][Once EXTENSION, SimpLHS] THEN
  SRW_TAC [][SET_IN_SINGC] THEN METIS_TAC []);
val _ = export_rewrites ["SINGC_11"]


val PAIRC_def = Define`PAIRC a b = SPEC0 (λx. (x = a) ∨ (x = b))`

val SINGC_PAIRC = store_thm(
  "SINGC_PAIRC",
  ``SINGC a = PAIRC a a``,
  SRW_TAC [][SINGC_def, PAIRC_def]);

val PCLASS_PAIRC_EMPTY = store_thm(
  "PCLASS_PAIRC_EMPTY",
  ``¬SET a ∧ ¬SET b ⇒ (PAIRC a b = {})``,
  SRW_TAC [][PAIRC_def, Once EXTENSION, SPEC0] THEN
  Cases_on `x = a` THEN SRW_TAC [][] THEN
  Cases_on `x = b` THEN SRW_TAC [][]);

val SET_IN_PAIRC = store_thm(
  "SET_IN_PAIRC",
  ``SET a ∧ SET b ⇒ (∀x. x ∈ PAIRC a b ⇔ (x = a) ∨ (x = b))``,
  SRW_TAC [CONJ_ss, DNF_ss][PAIRC_def, SPEC0]);

val UNORDERED_PAIRS = new_axiom(
  "UNORDERED_PAIRS",
  ``SET a ∧ SET b ⇒ ∃w. SET w ∧ a ∈ w ∧ b ∈ w``);

val PAIRC_SET_CLOSED = store_thm(
  "PAIRC_SET_CLOSED",
  ``SET a ∧ SET b ⇒ SET (PAIRC a b)``,
  DISCH_THEN (fn th => STRIP_ASSUME_TAC (MATCH_MP UNORDERED_PAIRS th) THEN
                       STRIP_ASSUME_TAC th) THEN
  MATCH_MP_TAC SUBSETS_ARE_SETS THEN Q.EXISTS_TAC `w` THEN
  SRW_TAC [][SUBSET_def, SET_IN_PAIRC] THEN SRW_TAC [][]);

val SINGC_SET = store_thm(
  "SINGC_SET",
  ``SET (SINGC a)``,
  Cases_on `SET a` THEN1 SRW_TAC [][SINGC_PAIRC, PAIRC_SET_CLOSED] THEN
  SRW_TAC [][PCLASS_SINGC_EMPTY]);
val _ = export_rewrites ["SINGC_SET"]

(* UNION ish operations *)

val UNION_def = Define`a ∪ b = SPEC0 (λx. x ∈ a ∨ x ∈ b)`

val IN_UNION = store_thm(
  "IN_UNION",
  ``x ∈ A ∪ B ⇔ x ∈ A ∨ x ∈ B``,
  SRW_TAC [][UNION_def, SPEC0] THEN METIS_TAC [SET_def]);
val _ = export_rewrites ["IN_UNION"]

val BIGUNION_def = Define`BIGUNION A = SPEC0 (λx. ∃y. y ∈ A ∧ x ∈ y)`
val IN_BIGUNION = store_thm(
  "IN_BIGUNION",
  ``x ∈ BIGUNION A ⇔ ∃y. y ∈ A ∧ x ∈ y``,
  SRW_TAC [][BIGUNION_def, SPEC0] THEN METIS_TAC [SET_def]);
val _ = export_rewrites ["IN_BIGUNION"]

val EMPTY_UNION = store_thm(
  "EMPTY_UNION",
  ``({} ∪ A = A) ∧ (A ∪ {} = A)``,
  SRW_TAC [][EXTENSION]);
val _ = export_rewrites ["EMPTY_UNION"]

val UNIONS = new_axiom(
  "UNIONS",
  ``SET a ⇒ ∃w. SET w ∧ ∀x y. x ∈ y ∧ y ∈ a ⇒ x ∈ w``);

val UNION_SET_CLOSED = store_thm(
  "UNION_SET_CLOSED",
  ``SET (A ∪ B) ⇔ SET A ∧ SET B``,
  Tactical.REVERSE EQ_TAC >| [
    STRIP_TAC THEN
    `SET (PAIRC A B)` by METIS_TAC [PAIRC_SET_CLOSED] THEN
    POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP UNIONS) THEN
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss)[SET_IN_PAIRC] THEN
    STRIP_TAC THEN MATCH_MP_TAC SUBSETS_ARE_SETS THEN Q.EXISTS_TAC `w` THEN
    SRW_TAC [][SUBSET_def] THEN SRW_TAC [][],
    strip_tac >> conj_tac >> match_mp_tac SUBSETS_ARE_SETS >>
    qexists_tac `A ∪ B` >> srw_tac [][SUBSET_def]
  ]);
val _ = export_rewrites ["UNION_SET_CLOSED"]

val BIGUNION_SET_CLOSED = store_thm(
  "BIGUNION_SET_CLOSED",
  ``SET A ⇒ SET (BIGUNION A)``,
  STRIP_TAC THEN IMP_RES_TAC UNIONS THEN MATCH_MP_TAC SUBSETS_ARE_SETS THEN
  Q.EXISTS_TAC `w` THEN ASM_SIMP_TAC (srw_ss()) [SUBSET_def] THEN
  METIS_TAC []);

(* intersections *)
val INTER_def = Define`
  s1 INTER s2 = SPEC0 (λe. e ∈ s1 ∧ e ∈ s2)
`;

val IN_INTER = store_thm(
  "IN_INTER",
  ``e ∈ s1 ∩ s2 ⇔ SET e ∧ e ∈ s1 ∧ e ∈ s2``,
  rw [INTER_def, SPEC0]);
val _ = export_rewrites ["IN_INTER"]

val INTER_SET_CLOSED = store_thm(
  "INTER_SET_CLOSED",
  ``(SET s1 ⇒ SET (s1 ∩ s2)) ∧ (SET s2 ⇒ SET (s1 ∩ s2))``,
  rpt strip_tac >> match_mp_tac SUBSETS_ARE_SETS >| [
    qexists_tac `s1`,
    qexists_tac `s2`
  ] >> rw[SUBSET_def]);
val _ = export_rewrites ["INTER_SET_CLOSED"]

val INSERT_def = Define`x INSERT y = SINGC x ∪ y`

val IN_INSERT = store_thm(
  "IN_INSERT",
  ``x ∈ a INSERT A ⇔ SET a ∧ (x = a) ∨ x ∈ A``,
  SRW_TAC [][INSERT_def] THEN Cases_on `SET a` THEN
  SRW_TAC [][SET_IN_SINGC, PCLASS_SINGC_EMPTY]);
val _ = export_rewrites ["IN_INSERT"]

val SET_INSERT = store_thm(
  "SET_INSERT",
  ``SET (x INSERT b) = SET b``,
  SRW_TAC [][INSERT_def])
val _ = export_rewrites ["SET_INSERT"]

val INSERT_IDEM = store_thm(
  "INSERT_IDEM",
  ``a INSERT a INSERT s = a INSERT s``,
  SRW_TAC [][Once EXTENSION] THEN METIS_TAC []);
val _ = export_rewrites ["INSERT_IDEM"]

val SUBSET_SING = store_thm(
  "SUBSET_SING",
  ``x ⊆ {a} ⇔ SET a ∧ (x = {a}) ∨ (x = {})``,
  SRW_TAC [][SUBSET_def] THEN EQ_TAC THENL [
    Cases_on `SET a` THEN SRW_TAC [][] THENL [
      Cases_on `x = {}` THEN SRW_TAC [][] THEN
      SRW_TAC [][Once EXTENSION] THEN
      `∃b. b ∈ x` by METIS_TAC [EMPTY_UNIQUE] THEN
      METIS_TAC [],
      METIS_TAC [EMPTY_UNIQUE]
    ],
    SIMP_TAC (srw_ss()) [DISJ_IMP_THM]
  ]);
val _ = export_rewrites ["SUBSET_SING"]

val BIGUNION_EMPTY = store_thm(
  "BIGUNION_EMPTY",
  ``(BIGUNION {} = {}) ∧ (BIGUNION {{}} = {})``,
  CONJ_TAC THEN SRW_TAC [][Once EXTENSION]);
val _ = export_rewrites ["BIGUNION_EMPTY"]

val BIGUNION_SING = store_thm(
  "BIGUNION_SING",
  ``SET a ⇒ (BIGUNION {a} = a)``,
  SRW_TAC [][Once EXTENSION]);

val BIGUNION_UNION = store_thm(
  "BIGUNION_UNION",
  ``SET a ∧ SET b ⇒ (BIGUNION {a;b} = a ∪ b)``,
  SRW_TAC [DNF_ss][Once EXTENSION]);

val POW_EMPTY = store_thm(
  "POW_EMPTY",
  ``POW {} = {{}}``,
  SRW_TAC [][Once EXTENSION] THEN SRW_TAC [CONJ_ss][]);

val POW_SING = store_thm(
  "POW_SING",
  ``SET a ⇒ (POW {a} = {{}; {a}})``,
  SRW_TAC [][Once EXTENSION] THEN
  ASM_SIMP_TAC (srw_ss() ++ CONJ_ss ++ DNF_ss) [] THEN
  METIS_TAC []);

(* "primitive ordered pair" *)
val POPAIR_def = Define`POPAIR a b = {{a}; {a;b}}`

val POPAIR_SET = store_thm(
  "POPAIR_SET",
  ``SET (POPAIR a b)``,
  SRW_TAC [][POPAIR_def]);
val _ = export_rewrites ["POPAIR_SET"]

val SING_11 = store_thm(
  "SING_11",
  ``SET a ∧ SET b ⇒ (({a} = {b}) = (a = b))``,
  STRIP_TAC THEN ASM_SIMP_TAC (srw_ss()) [SimpLHS, Once EXTENSION] THEN
  SRW_TAC [][] THEN METIS_TAC []);

val SING_EQ_PAIR = store_thm(
  "SING_EQ_PAIR",
  ``SET a ∧ SET b ∧ SET c ⇒ (({a;b} = {c}) = (a = b) ∧ (b = c))``,
  STRIP_TAC THEN ASM_SIMP_TAC (srw_ss()) [SimpLHS, Once EXTENSION] THEN
  SRW_TAC [][] THEN METIS_TAC []);

val PAIR_EQ_PAIR = store_thm(
  "PAIR_EQ_PAIR",
  ``SET a ∧ SET b ∧ SET c ∧ SET d ⇒
    (({a;b} = {c;d}) ⇔ (a = c) ∧ (b = d) ∨ (a = d) ∧ (b = c))``,
  STRIP_TAC THEN ASM_SIMP_TAC (srw_ss()) [Once EXTENSION, SimpLHS] THEN
  SRW_TAC [][] THEN METIS_TAC []);

val POPAIR_INJ = store_thm(
  "POPAIR_INJ",
  ``SET a ∧ SET b ∧ SET c ∧ SET d ⇒
    ((POPAIR a b = POPAIR c d) ⇔ (a = c) ∧ (b = d))``,
  STRIP_TAC THEN SRW_TAC [][SimpLHS, Once EXTENSION] THEN
  SRW_TAC [][POPAIR_def] THEN REVERSE EQ_TAC THEN1 SRW_TAC [][] THEN
  METIS_TAC [SING_11, SING_EQ_PAIR, PAIR_EQ_PAIR]);

(* ordered pairs that work when classes are involved *)
val OPAIR_def = Define`
  OPAIR a b = SPEC0 (λx. ∃y. y ∈ a ∧ (x = POPAIR {} y)) ∪
              SPEC0 (λx. ∃y. y ∈ b ∧ (x = POPAIR {{}} y))
`;

val SET_OPAIR = store_thm(
  "SET_OPAIR",
  ``SET a ∧ SET b ⇒ SET (OPAIR a b)``,
  SRW_TAC [][OPAIR_def] THENL[
    SRW_TAC [][POPAIR_def] THEN MATCH_MP_TAC SUBSETS_ARE_SETS THEN
    SRW_TAC [DNF_ss][SUBSET_def, SPEC0] THEN
    Q.EXISTS_TAC `POW (POW (a ∪ {{}}))` THEN
    SRW_TAC [][POW_SET_CLOSED] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [SUBSET_def],
    SRW_TAC [][POPAIR_def] THEN MATCH_MP_TAC SUBSETS_ARE_SETS THEN
    SRW_TAC [DNF_ss][SUBSET_def, SPEC0] THEN
    Q.EXISTS_TAC `POW (POW (b ∪ {{{}}}))` THEN
    SRW_TAC [][POW_SET_CLOSED] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [SUBSET_def]
  ]);
val _ = export_rewrites ["SET_OPAIR"]

val ZERO_NEQ_ONE = store_thm(
  "ZERO_NEQ_ONE",
  ``{} ≠ {{}}``,
  SRW_TAC [][EXTENSION] THEN Q.EXISTS_TAC `{}` THEN SRW_TAC [][]);
val _ = export_rewrites ["ZERO_NEQ_ONE"]

val POPAIR_01 = store_thm(
  "POPAIR_01",
  ``POPAIR {} x ≠ POPAIR {{}} y``,
  SRW_TAC [][POPAIR_def] THEN SRW_TAC [][Once EXTENSION] THEN
  Q.EXISTS_TAC `{{}}` THEN SRW_TAC [][SING_11] THEN
  SRW_TAC [][Once EXTENSION] THEN Q.EXISTS_TAC `{{}}` THEN
  SRW_TAC [][]);

val OPAIR_11 = store_thm(
  "OPAIR_11",
  ``((OPAIR a b = OPAIR c d) ⇔ (a = c) ∧ (b = d))``,
  SRW_TAC [][Once EXTENSION, SimpLHS] THEN
  SRW_TAC [][OPAIR_def, SPEC0] THEN
  REVERSE EQ_TAC THEN1 SRW_TAC [][] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC (srw_ss()) [EXTENSION, EQ_IMP_THM] THEN
    Q.X_GEN_TAC `e` THEN REPEAT STRIP_TAC THEN
    `SET e` by METIS_TAC [SET_def] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `POPAIR {} e` MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [POPAIR_01] THENL [
      DISCH_THEN (MP_TAC o CONV_RULE LEFT_IMP_EXISTS_CONV o #1 o
                  EQ_IMP_RULE),
      DISCH_THEN (MP_TAC o CONV_RULE LEFT_IMP_EXISTS_CONV o #2 o
                  EQ_IMP_RULE)
    ] THEN
    DISCH_THEN (Q.SPEC_THEN `e` MP_TAC) THEN SRW_TAC [][] THEN
    POP_ASSUM MP_TAC THEN
    `SET y` by METIS_TAC [SET_def] THEN
    SRW_TAC [][POPAIR_INJ],

    SIMP_TAC (srw_ss()) [EXTENSION, EQ_IMP_THM] THEN
    Q.X_GEN_TAC `e` THEN REPEAT STRIP_TAC THEN
    `SET e` by METIS_TAC [SET_def] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `POPAIR {{}} e` MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [POPAIR_01] THENL [
      DISCH_THEN (MP_TAC o CONV_RULE LEFT_IMP_EXISTS_CONV o #1 o
                  EQ_IMP_RULE),
      DISCH_THEN (MP_TAC o CONV_RULE LEFT_IMP_EXISTS_CONV o #2 o
                  EQ_IMP_RULE)
    ] THEN
    DISCH_THEN (Q.SPEC_THEN `e` MP_TAC) THEN SRW_TAC [][] THEN
    POP_ASSUM MP_TAC THEN
    `SET y` by METIS_TAC [SET_def] THEN
    SRW_TAC [][POPAIR_INJ]
  ]);
val _ = export_rewrites ["OPAIR_11"]

val _ = add_rule { fixity = Closefix,
                   term_name = "OPAIR",
                   block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "〈", TM, HardSpace 1,
                                  TOK "·", BreakSpace(1,2),
                                  TM, TOK "〉"]}

val CROSS_def = Define`
  s1 CROSS s2 = SPEC0 (λx. ∃a b. a ∈ s1 ∧ b ∈ s2 ∧ (x = 〈a · b〉))
`;

val FunSpace_def = Define`
  FunSpace A B = SPEC0 (λf. f ⊆ A × B ∧ ∀a. a ∈ A ⇒ ∃!b. 〈a · b〉 ∈ f)
`

val id_def = Define`
  id A = SPEC0 (λx. ∃a. a ∈ A ∧ (x = 〈a·a〉))
`;

(*
val apply_def = new_specification("apply_def",
  ["apply"],
  CONV_RULE SKOLEM_CONV
            (prove(``∀f x A B. f ∈ FunSpace A B ∧ x ∈ A ⇒
                               ∃y. y ∈ B ∧ 〈x·y〉 ∈ f``,
                   SRW_TAC [][FunSpace_def, SPEC0, CROSS_def] THEN
                   RES_TAC THEN
                   FULL_SIMP_TAC (srw_ss()) [EXISTS_UNIQUE_THM] THEN
                   Q.EXISTS_TAC `b` THEN SRW_TAC [][] THEN
                   FULL_SIMP_TAC (srw_ss()) [SUBSET_def, SPEC0] THEN
                   RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [OPAIR_11])
*)

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

val vSUC_IN_Nats = store_thm(
  "vSUC_IN_Nats",
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
  qx_gen_tac `n` >> rw [Nats_def, SPEC0] >>
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
      vSUC_IN_Nats]);

val Nats_least_inductive = store_thm(
  "Nats_least_inductive",
  ``P ∈ Inductives ⇒ Nats ⊆ P``,
  rw[Inductives_def, SPEC0, SUBSET_def] >>
  fs [Nats_def, SPEC0, inductive_def])

val Nats_SETs = prove(``n ∈ Nats ⇒ SET n``, metis_tac [SET_def])
val _ = augment_srw_ss [rewrites [Nats_SETs]]
(*
Higher order logic wins here: can capture all possible predicates.
Can simplify to membership of a set S by making the predicate P be just that.
 ⊢ ∀P. P {} ∧ (∀x. P x ∧ x ∈ Nats ⇒ P (vSUC x)) ⇒ ∀u. u ∈ Nats ⇒ P u
*)
val nat_induction = save_thm(
  "nat_induction",
  Nats_least_inductive
      |> SIMP_RULE(srw_ss())[SUBSET_def,Inductives_def,SPEC0]
      |> Q.GEN `P`
      |> Q.SPEC `SPEC0 P ∩ Nats`
      |> SIMP_RULE (srw_ss() ++ CONJ_ss)
                   [Nats_SET, EMPTY_IN_Nats, vSUC_IN_Nats, SPEC0,
                    GSYM fromNat_def]
      |> Q.GEN `P`);

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

val Nats_not_selfmembers = store_thm(
  "Nats_not_selfmembers",
  ``∀n. n ∈ Nats ⇒ n ∉ n``,
  ho_match_mp_tac nat_induction >> rw[vSUC_def] >| [
    strip_tac >> `n ∈ n ∪ {n}` by rw[] >>
    metis_tac [Nats_transitive, transitive_ALT],
    rw[Once EXTENSION] >> metis_tac []
  ]);

val pre_IN_vSUC = store_thm(
  "pre_IN_vSUC",
  ``SET n ⇒ n ∈ vSUC n``,
  rw[vSUC_def]);

val SET_vSUC = store_thm(
  "SET_vSUC",
  ``SET (vSUC n) = SET n``,
  rw[vSUC_def, EQ_IMP_THM]);
val _ = export_rewrites ["SET_vSUC"]

val vSUC_11 = store_thm(
  "vSUC_11",
  ``∀n m. n ∈ Nats ∧ m ∈ Nats ⇒ ((vSUC n = vSUC m) ⇔ (n = m))``,
  rw[EQ_IMP_THM] >>
  `n ∈ vSUC m` by metis_tac [pre_IN_vSUC, SET_vSUC, Nats_SETs] >>
  pop_assum mp_tac >> rw[vSUC_def] >>
  `m ∈ vSUC n` by metis_tac [pre_IN_vSUC, SET_vSUC, Nats_SETs] >>
  fs[vSUC_def] >>
  metis_tac [transitive_ALT, Nats_transitive, Nats_not_selfmembers]);
val _ = export_rewrites ["vSUC_11"]


(*
val FORMATION = new_axiom(

*)

val _ = export_theory()
