(* Playing around with what is really Morse-Kelley set theory *)

open HolKernel boolLib bossLib Parse
open boolSimps

val _ = new_theory "vbgset"
val _ = ParseExtras.temp_loose_equality()

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
val _ = export_rewrites ["SPEC0"]

val EMPTY_def = Define`EMPTY = SPEC0 (λx. F)`

val NOT_IN_EMPTY = store_thm(
  "NOT_IN_EMPTY",
  ``x ∉ {}``,
  SRW_TAC [][EMPTY_def]);
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
  SRW_TAC [][Sets_def]);

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
    |> (SIMP_CONV bool_ss [RUS_def, Once SPEC0] THENC
        SIMP_CONV bool_ss [GSYM RUS_def])

val RUS_not_SET = store_thm(
  "RUS_not_SET",
  ``¬ SET RUS``,
  METIS_TAC [RUSlemma]);

val POW_def = Define`POW A = SPEC0 (λx. x ⊆ A)`
val IN_POW = store_thm(
  "IN_POW",
  ``x ∈ POW A ⇔ SET x ∧ x ⊆ A``,
  SRW_TAC [][POW_def]);
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
  SRW_TAC [][SINGC_def, Once EXTENSION]);

val SET_IN_SINGC = store_thm(
  "SET_IN_SINGC",
  ``SET a ⇒ (x ∈ SINGC a ⇔ (x = a))``,
  SRW_TAC [CONJ_ss][SINGC_def]);

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
  SRW_TAC [][PAIRC_def, Once EXTENSION] THEN
  Cases_on `x = a` THEN SRW_TAC [][] THEN
  Cases_on `x = b` THEN SRW_TAC [][]);

val SET_IN_PAIRC = store_thm(
  "SET_IN_PAIRC",
  ``SET a ∧ SET b ⇒ (∀x. x ∈ PAIRC a b ⇔ (x = a) ∨ (x = b))``,
  SRW_TAC [CONJ_ss, DNF_ss][PAIRC_def]);

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
  SRW_TAC [][UNION_def] THEN METIS_TAC [SET_def]);
val _ = export_rewrites ["IN_UNION"]

val BIGUNION_def = Define`BIGUNION A = SPEC0 (λx. ∃y. y ∈ A ∧ x ∈ y)`
val IN_BIGUNION = store_thm(
  "IN_BIGUNION",
  ``x ∈ BIGUNION A ⇔ ∃y. y ∈ A ∧ x ∈ y``,
  SRW_TAC [][BIGUNION_def] THEN METIS_TAC [SET_def]);
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
  rw [INTER_def]);
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
    SRW_TAC [DNF_ss][SUBSET_def] THEN
    Q.EXISTS_TAC `POW (POW (a ∪ {{}}))` THEN
    SRW_TAC [][POW_SET_CLOSED] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [SUBSET_def],
    SRW_TAC [][POPAIR_def] THEN MATCH_MP_TAC SUBSETS_ARE_SETS THEN
    SRW_TAC [DNF_ss][SUBSET_def] THEN
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
  SRW_TAC [][OPAIR_def] THEN
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


(*
val FORMATION = new_axiom(

*)

val FOUNDATION = new_axiom(
  "FOUNDATION",
  ``(∀a. SET a ∧ a ⊆ w ⇒ a ∈ w) ⇒ ∀a. SET a ⇒ a ∈ w``);

val IN_INDUCTION = store_thm(
  "IN_INDUCTION",
  ``(∀a. SET a ∧ (∀x. x ∈ a ⇒ P x) ⇒ P a) ⇒ ∀a. SET a ⇒ P a``,
  rpt strip_tac >>
  MP_TAC (INST [``w:vbgc`` |-> ``SPEC0 (λx. P x)``] FOUNDATION) >>
  rw[SUBSET_def]);
val _ = IndDefLib.export_rule_induction "IN_INDUCTION"

val IN_REFL = store_thm(
  "IN_REFL",
  ``x ∉ x``,
  Cases_on `SET x` >| [
    pop_assum mp_tac >> qid_spec_tac `x` >>
    ho_match_mp_tac IN_INDUCTION >> metis_tac [],
    fs[SET_def]
  ]);
val _ = export_rewrites ["IN_REFL"]

val IN_ANTISYM = store_thm(
  "IN_ANTISYM",
  ``x ∈ y ∧ y ∈ x ⇔ F``,
  qsuff_tac `∀x. SET x ⇒ ∀y. y ∈ x ⇒ x ∉ y` >- metis_tac [SET_def] >>
  Induct_on `SET x` >> metis_tac []);

val IN3_ANTISYM = store_thm(
  "IN3_ANTISYM",
  ``x ∈ y ∧ y ∈ z ∧ z ∈ x ⇔ F``,
  qsuff_tac `∀x. SET x ⇒ ∀y z. y ∈ z ∧ z ∈ x ⇒ x ∉ y` >- metis_tac [SET_def] >>
  Induct_on `SET x` >> metis_tac []);

val FORMATION = new_axiom(
  "FORMATION",
  ``SET a ∧ (∀x. x ∈ a ⇒ ∃!y. P x y) ∧ (∀x y. x ∈ a ∧ P x y ⇒ SET y) ⇒
    ∃w. SET w ∧ ∀y. y ∈ w ⇔ ∃x. x ∈ a ∧ P x y``);

val bad_def = with_flag (computeLib.auto_import_definitions, false) Define`
  bad f a = SET a ∧ (∀i. SET (f i)) ∧ (f 0 = {a}) ∧
            (∀i x. x ∈ f i ⇒ x ∩ f (i + 1) ≠ {})
`;

val FOUNDATION2 = store_thm(
  "FOUNDATION2",
  ``¬∃f:num -> vbgc.
       (∀i. SET (f i)) ∧ (∃e. SET e ∧ (f 0 = {e})) ∧
       (∀i x. x ∈ f i ⇒ x ∩ f (i + 1) ≠ {})``,
  qsuff_tac `∀a. SET a ⇒ ¬∃f. bad f a`
    >- (rw[bad_def] >>
        Tactical.REVERSE (Cases_on `∀i. SET (f i)`) >- metis_tac [] >>
        rw[] >> Cases_on `∃e. f 0 = {e}` >> fs[] >>
        Tactical.REVERSE (Cases_on `SET e`)
          >- (DISJ1_TAC >> rw[Once EXTENSION]) >>
        DISJ2_TAC >>
        first_x_assum (qspec_then `e` mp_tac) >> rw[] >>
        metis_tac []) >>
  Induct_on `SET a` >> qx_gen_tac `a` >> Cases_on `SET a` >> simp[] >>
  CONV_TAC CONTRAPOS_CONV >> rw[] >>
  `a ∈ f 0` by metis_tac [IN_INSERT, bad_def] >>
  `a ∩ f 1 ≠ {}` by metis_tac [bad_def, DECIDE ``0 + 1 = 1``] >>
  `∃b. b ∈ a ∩ f 1` by metis_tac [EMPTY_UNIQUE] >>
  qabbrev_tac `
    poor = λp. (∀i. p i ⊆ f (i + 1)) ∧ b ∈ p 0 ∧
               (∀i x. x ∈ p i ⇒ x ∩ f (i + 2) ⊆ p (i + 1))
  ` >>
  qabbrev_tac `P = λn. f (n + 1)` >>
  `poor P`
     by (srw_tac[ARITH_ss][Abbr`P`,Abbr`poor`] >> fs[] >>
         rw[SUBSET_def]) >>
  qabbrev_tac `N = λn. SPEC0 (λx. ∀p. poor p ⇒ x ∈ p n)` >>
  `b ∈ N 0`
     by (rw[Abbr`N`] >- metis_tac [SET_def] >> fs[Abbr`poor`]) >>
  `poor N`
     by (qpat_assum `Abbrev(poor = X)`
                    (fn th => ASSUME_TAC th THEN MP_TAC th) >>
         disch_then (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         BETA_TAC >> ASM_REWRITE_TAC[] >> rpt strip_tac >| [
           qsuff_tac `N i ⊆ P i` >- metis_tac [SUBSET_def] >>
           rw[Abbr`N`, SUBSET_def],
           `∀p. poor p ⇒ x ∩ f(i + 2) ⊆ p (i + 1)`
              by (rpt strip_tac >>
                  `x ∈ p i` by fs[Abbr`N`, Abbr`poor`] >>
                  metis_tac []) >>
           rw[Abbr`N`, SUBSET_def] >> metis_tac [SUBSET_def, IN_INTER]
         ]) >>
  qexists_tac `b` >> fs[] >>
  `∀p. poor p ⇒ ∀n. SET (p n)`
     by (rw[Abbr`poor`] >> match_mp_tac SUBSETS_ARE_SETS  >>
         qexists_tac `f (n + 1)` >> fs[bad_def]) >>
  qexists_tac `N` >> rw[bad_def] >|[
    rw[Once EXTENSION, EQ_IMP_THM] >>
    spose_not_then assume_tac >>
    qpat_assum `x ∈ N 0` mp_tac >>
    qpat_assum `Abbrev(N = X)`
      (fn th => ASSUME_TAC th >>
                MP_TAC (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
    disch_then SUBST1_TAC >> BETA_TAC >> rw[] >> DISJ2_TAC >>
    qexists_tac `λn. if n = 0 then SPEC0 (λy. y ∈ N 0 ∧ y ≠ x) else N n` >>
    rw[] >>
    qpat_assum `Abbrev(poor = X)`
      (fn th => assume_tac th >>
                SUBST1_TAC (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
    BETA_TAC >> ASM_REWRITE_TAC [] THEN BETA_TAC >> simp[] >> conj_tac
      >- (rw[SUBSET_def] >>
          qpat_assum `poor N` mp_tac >>
          rw[Abbr`poor`] >> metis_tac [SUBSET_def, DECIDE ``0 + 1 = 1``]) >>
    map_every qx_gen_tac [`i`, `y`] >>
    rw[] >> metis_tac [DECIDE ``(0 + 1 = 1) ∧ (0 + 2 = 2)``],
    `x ∈ f (i + 1)` by metis_tac[SUBSET_def] >>
    `x ∩ f(i + 2) ⊆ N (i + 1)` by metis_tac [] >>
    `x ∩ f(i + 2) ≠ {}` by metis_tac [bad_def, DECIDE ``i + 1 + 1 = i + 2``] >>
    simp[EXTENSION] >> metis_tac[SET_def, EMPTY_UNIQUE, IN_INTER, SUBSET_def]
  ])

val lemma0 = prove(
  ``SET ss ⇒ SET ss ∧ ∀x. x ∈ ss ⇒ SET (x ∩ a)``,
  rw[] >> match_mp_tac SUBSETS_ARE_SETS >> qexists_tac `x` >>
  rw[SUBSET_def] >> metis_tac [SET_def])
val formlemma =
    FORMATION |> Q.INST [`a` |-> `ss`,
                         `P` |-> `λx y. (y = x ∩ a)`]
              |> SIMP_RULE (srw_ss()) []
              |> C MP (UNDISCH lemma0)

val FOUNDATION3 = store_thm(
  "FOUNDATION3",
  ``∀a. a ≠ {} ⇒ ∃x. x ∈ a ∧ (x ∩ a = {})``,
  spose_not_then strip_assume_tac >>
  `∃b. b ∈ a` by metis_tac [EMPTY_UNIQUE] >>
  qabbrev_tac `
     m = PRIM_REC {b} (λs n. BIGUNION (SPEC0 (λy. ∃x. x ∈ s ∧ (y = x ∩ a))))
  ` >>
  `∀i. m i ⊆ a`
     by (Induct >> rw[Abbr`m`, prim_recTheory.PRIM_REC_THM, SUBSET_def] >>
         fs[]) >>
  `∀i. SET (m i)`
     by (Induct >> rw[Abbr`m`, prim_recTheory.PRIM_REC_THM] >>
         match_mp_tac BIGUNION_SET_CLOSED >>
         qpat_assum `SET sss` mp_tac >>
         qmatch_abbrev_tac `SET ss ⇒ SET sss` >>
         qunabbrev_tac `sss` >> strip_tac >>
         strip_assume_tac formlemma >>
         qsuff_tac `SPEC0 (λy. ∃x. x ∈ ss ∧ (y = x ∩ a)) = w` >- rw[] >>
         simp[Once EXTENSION, EQ_IMP_THM] >>
         asm_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `y` >> strip_tac >>
         match_mp_tac SUBSETS_ARE_SETS >> qexists_tac `y` >>
         metis_tac [SUBSET_def, SET_def, IN_INTER]) >>
  `bad m b`
     by (rw[bad_def]
            >- metis_tac [SET_def]
            >- rw[Abbr`m`, prim_recTheory.PRIM_REC_THM]
            >- (`x ∈ a` by metis_tac [SUBSET_def] >>
                `x ∩ a ≠ {}` by metis_tac [] >>
                `∃y. y ∈ x ∩ a` by metis_tac [EMPTY_UNIQUE] >>
                `y ∈ m (SUC i)`
                   by (rw[Abbr`m`, prim_recTheory.PRIM_REC_THM] >>
                       srw_tac [DNF_ss][] >>
                       qexists_tac `x` >> rw[]
                         >- (match_mp_tac SUBSETS_ARE_SETS >>
                             qexists_tac `x` >>
                             metis_tac [SUBSET_def, IN_INTER, SET_def])
                         >- metis_tac [SET_def]
                         >> fs[]) >>
                fs[arithmeticTheory.ADD1] >>
                rw[Once EXTENSION] >> metis_tac [SET_def])) >>
  MP_TAC (FOUNDATION2 |> SIMP_RULE bool_ss []
                      |> Q.SPEC `m`) >>
  simp[] >> conj_tac
     >- (qexists_tac `b` >> rw[Abbr`m`, prim_recTheory.PRIM_REC_THM] >>
         metis_tac [SET_def]) >>
  metis_tac [bad_def])

val _ = delete_const "bad"

val _ = export_theory()
