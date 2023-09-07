(* res_quanScript.sml - Development of restricted quantifiers

BY: Wai Wong
DATE: 1 Aug 92
CHANGED BY: Joe Hurd, June 2001 (to use predicate sets)
CHANGED BY: Joe Hurd, June 2001 (to remove the ARB from RES_ABSTRACT)
CHANGED BY: Joe Hurd, October 2001 (moved definitions to boolTheory)

============================================================================*)

open HolKernel Parse boolLib combinTheory pred_setTheory simpLib pred_setSimps
  boolSimps BasicProvers;

val _ = new_theory "res_quan";

(* --------------------------------------------------------------------- *)
(* Support theorems and code (not exported)                              *)
(* --------------------------------------------------------------------- *)

fun simp thml = ASM_SIMP_TAC (bool_ss ++ pred_setSimps.PRED_SET_ss) thml;
val CONJ_AC = AC CONJ_COMM CONJ_ASSOC;
val ELIM_EXISTS_IMP = GSYM boolTheory.LEFT_FORALL_IMP_THM;

val EMPTY = prove(
  ``!s. (s = {}) <=> !x. x NOTIN s``,
  prove_tac [MEMBER_NOT_EMPTY]);

(* --------------------------------------------------------------------- *)
(* Definitions to support restricted abstractions and quantifications    *)
(* --------------------------------------------------------------------- *)

(* JEH: Defns moved to boolTheory: the following versions remove lambdas *)

val RES_FORALL = save_thm("RES_FORALL", RES_FORALL_THM);
val RES_EXISTS = save_thm("RES_EXISTS", RES_EXISTS_THM);
val RES_EXISTS_UNIQUE = save_thm("RES_EXISTS_UNIQUE", RES_EXISTS_UNIQUE_THM);
val RES_SELECT = save_thm("RES_SELECT", RES_SELECT_THM);
Theorem RES_ABSTRACT = cj 1 RES_ABSTRACT_DEF

(* ===================================================================== *)
(* Properties of restricted quantification.                              *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* RES_FORALL                                                            *)
(* --------------------------------------------------------------------- *)

Theorem RES_FORALL_CONJ_DIST:
  !P Q R.
     (!(i:'a)::P. (Q i /\ R i)) <=> (!i::P. Q i) /\ (!i::P. R i)
Proof
    REPEAT STRIP_TAC >> REWRITE_TAC [RES_FORALL]
    >> BETA_TAC >> EQ_TAC >> REPEAT STRIP_TAC >> RES_TAC
QED

Theorem RES_FORALL_DISJ_DIST:
  !P Q R.
     (!(i:'a)::(\j. P j \/ Q j). R i) <=> (!i::P. R i) /\ (!i::Q. R i)
Proof
    REPEAT STRIP_TAC >> REWRITE_TAC [RES_FORALL, SPECIFICATION] >>
    BETA_TAC >> EQ_TAC >> REPEAT STRIP_TAC >> RES_TAC
QED

val RES_FORALL_UNIQUE = store_thm("RES_FORALL_UNIQUE",
    (``!P j. (!(i:'a)::($= j). P i) = P j``),
    REWRITE_TAC [RES_FORALL, SPECIFICATION] >> BETA_TAC >>
    PROVE_TAC []);

val RES_FORALL_FORALL = store_thm("RES_FORALL_FORALL",
    (``!(P:'a->bool) (R:'a->'b->bool) (x:'b).
        (!x. !i::P. R i x) = (!i::P. !x. R i x)``),
    REPEAT STRIP_TAC >> REWRITE_TAC [RES_FORALL, SPECIFICATION]
    >> BETA_TAC >> EQ_TAC >> REPEAT STRIP_TAC >> RES_TAC
    >> FIRST_ASSUM MATCH_ACCEPT_TAC);

val RES_FORALL_REORDER = store_thm("RES_FORALL_REORDER",
    (``!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (!i::P. !j::Q. R i j) = (!j::Q. !i::P. R i j)``),
    REPEAT STRIP_TAC >> REWRITE_TAC [RES_FORALL, SPECIFICATION] >>
    BETA_TAC >> EQ_TAC >> REPEAT STRIP_TAC >> RES_TAC);

val RES_FORALL_T = store_thm(
  "RES_FORALL_T",
  ``!P s x. !x::s. T``,
  simp [RES_FORALL_TRUE]);

val RES_FORALL_F = store_thm(
  "RES_FORALL_F",
  ``!P s x. (!x::s. F) <=> (s = {})``,
  simp [RES_FORALL, EMPTY]);

val RES_FORALL_EMPTY = store_thm
  ("RES_FORALL_EMPTY",
   ``!(p : 'a -> bool). RES_FORALL {} p``,
   RW_TAC bool_ss [RES_FORALL, NOT_IN_EMPTY]);

val RES_FORALL_UNIV = store_thm
  ("RES_FORALL_UNIV",
   ``!(p : 'a -> bool). RES_FORALL UNIV p = $! p``,
   RW_TAC bool_ss [RES_FORALL, IN_UNIV, ETA_AX]);

val RES_FORALL_NULL = store_thm
  ("RES_FORALL_NULL",
   ``!(p : 'a -> bool) m. RES_FORALL p (\x. m) = ((p = {}) \/ m)``,
   RW_TAC bool_ss [RES_FORALL, EXTENSION, NOT_IN_EMPTY]
   >> Cases_on `m`
   >> PROVE_TAC []);

val NOT_RES_FORALL = store_thm(
  "NOT_RES_FORALL",
  ``!P s. ~(!x::s. P x) <=> ?x::s. ~P x``,
  simp [RES_FORALL, RES_EXISTS]);

val RES_FORALL_NOT_EMPTY = store_thm(
  "RES_FORALL_NOT_EMPTY",
  ``!P s. ~RES_FORALL s P ==> (s <> {})``,
  rpt strip_tac >>
  `RES_FORALL s P` suffices_by (simp []) >>
  pop_assum SUBST1_TAC >>
  MATCH_ACCEPT_TAC RES_FORALL_EMPTY);

val RES_FORALL_SUBSET = store_thm(
  "RES_FORALL_SUBSET",
  ``!P s t. s SUBSET t ==> RES_FORALL t P ==> RES_FORALL s P``,
  simp [RES_FORALL, SUBSET_DEF]);

val RES_FORALL_UNION = store_thm(
  "RES_FORALL_UNION",
  ``!P s t. RES_FORALL (s UNION t) P <=> RES_FORALL s P /\ RES_FORALL t P``,
  asm_simp_tac (bool_ss ++ DNF_ss ++ PRED_SET_ss) [RES_FORALL]);

val RES_FORALL_DIFF = store_thm(
  "RES_FORALL_DIFF",
  ``!P s t x. (!x::s DIFF t. P x) <=> !x::s. x NOTIN t ==> P x``,
  simp [RES_FORALL, AND_IMP_INTRO]);

val IN_BIGINTER_RES_FORALL = store_thm(
  "IN_BIGINTER_RES_FORALL",
  ``!x sos. x IN BIGINTER sos <=> !s::sos. x IN s``,
  simp [RES_FORALL]);

val RES_FORALL_BIGUNION = store_thm(
  "RES_FORALL_BIGUNION",
  ``!P sos. (!x::BIGUNION sos. P x) <=> !(s::sos) (x::s). P x``,
  simp [RES_FORALL, IN_BIGUNION] >>
  prove_tac []);

val RES_FORALL_BIGINTER = store_thm(
  "RES_FORALL_BIGINTER",
  ``!P sos. (!x::BIGINTER sos. P x) <=> !x. (!s::sos. x IN s) ==> P x``,
  simp [RES_FORALL]);

(* --------------------------------------------------------------------- *)
(* RES_EXISTS                                                            *)
(* --------------------------------------------------------------------- *)

Theorem RES_EXISTS_DISJ_DIST:
  !P Q R.
     (?(i:'a)::P. (Q i \/ R i)) <=> (?i::P. Q i) \/ (?i::P. R i)
Proof
    REPEAT STRIP_TAC >> REWRITE_TAC [RES_EXISTS, SPECIFICATION]
    >> BETA_TAC >> PURE_ONCE_REWRITE_TAC[CONJ_SYM]
    >> PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    >> CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) >> REFL_TAC
QED

Theorem RES_DISJ_EXISTS_DIST:
  !P Q R.
     (?(i:'a)::(\i. P i \/ Q i). R i) <=> (?i::P. R i) \/ (?i::Q. R i)
Proof
    REPEAT STRIP_TAC >> REWRITE_TAC [RES_EXISTS, SPECIFICATION]
    >> BETA_TAC >> PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    >> CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) >> REFL_TAC
QED

val RES_EXISTS_EQUAL = store_thm("RES_EXISTS_EQUAL",
    (``!P j. (?(i:'a)::($= j). P i) = P j``),
    REWRITE_TAC [RES_EXISTS, SPECIFICATION] >> BETA_TAC >> REPEAT GEN_TAC
    >> EQ_TAC >|[
      DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) >> ASM_REWRITE_TAC[],
      DISCH_TAC >> EXISTS_TAC (``j:'a``) >>  ASM_REWRITE_TAC[]]);

val RES_EXISTS_REORDER = store_thm("RES_EXISTS_REORDER",
    (``!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (?i::P. ?j::Q. R i j) = (?j::Q. ?i::P. R i j)``),
    REPEAT STRIP_TAC >> REWRITE_TAC [RES_EXISTS, SPECIFICATION] >> BETA_TAC
    >> EQ_TAC >> DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) >|[
      EXISTS_TAC (``x':'b``) >> CONJ_TAC >|[
        ALL_TAC, EXISTS_TAC ``x:'a`` >> CONJ_TAC],
      EXISTS_TAC ``x':'a`` >> CONJ_TAC >|[
        ALL_TAC, EXISTS_TAC ``x:'b`` >> CONJ_TAC]]
    >> FIRST_ASSUM ACCEPT_TAC);

val RES_EXISTS_F = store_thm(
  "RES_EXISTS_F",
  ``!P s x. ~?s::x. F``,
  simp [RES_EXISTS_FALSE]);

val RES_EXISTS_T = store_thm(
  "RES_EXISTS_T",
  ``!P s x. (?x::s. T) <=> (s <> {})``,
  simp [RES_EXISTS, EMPTY]);

val RES_EXISTS_EMPTY = store_thm
  ("RES_EXISTS_EMPTY",
   ``!(p : 'a -> bool). ~RES_EXISTS {} p``,
   RW_TAC bool_ss [RES_EXISTS, NOT_IN_EMPTY]);

val RES_EXISTS_UNIV = store_thm
  ("RES_EXISTS_UNIV",
   ``!(p : 'a -> bool). RES_EXISTS UNIV p = $? p``,
   RW_TAC bool_ss [RES_EXISTS, IN_UNIV, ETA_AX]);

val RES_EXISTS_NULL = store_thm
  ("RES_EXISTS_NULL",
   ``!(p : 'a -> bool) m. RES_EXISTS p (\x. m) = (~(p = {}) /\ m)``,
   RW_TAC bool_ss [RES_EXISTS, EXTENSION, NOT_IN_EMPTY]
   >> Cases_on `m`
   >> PROVE_TAC []);

Theorem RES_EXISTS_ALT:
  !(p : 'a -> bool) m.
      RES_EXISTS p m <=> (RES_SELECT p m) IN p /\ m (RES_SELECT p m)
Proof
   RW_TAC bool_ss [RES_EXISTS, EXISTS_DEF, RES_SELECT, SPECIFICATION]
QED

val NOT_RES_EXISTS = store_thm(
  "NOT_RES_EXISTS",
  ``!P s. ~(?x::s. P x) <=> !x::s. ~P x``,
  simp [RES_FORALL, RES_EXISTS, GSYM IMP_DISJ_THM]);

val RES_EXISTS_NOT_EMPTY = store_thm(
  "RES_EXISTS_NOT_EMPTY",
  ``!P s. RES_EXISTS s P ==> (s <> {})``,
  rpt strip_tac >>
  `~RES_EXISTS s P` suffices_by simp [] >>
  pop_assum SUBST1_TAC >>
  MATCH_ACCEPT_TAC RES_EXISTS_EMPTY);

val RES_EXISTS_SUBSET = store_thm(
  "RES_EXISTS_SUBSET",
  ``!P s t. s SUBSET t ==> RES_EXISTS s P ==> RES_EXISTS t P``,
  simp [RES_EXISTS, SUBSET_DEF] >>
  prove_tac []);

val RES_EXISTS_UNION = store_thm(
  "RES_EXISTS_UNION",
  ``!P s t. RES_EXISTS (s UNION t) P <=> RES_EXISTS s P \/ RES_EXISTS t P``,
  simp [RES_EXISTS] >>
  prove_tac []);

val RES_EXISTS_DIFF = store_thm(
  "RES_EXISTS_DIFF",
  ``!P s t x. (?x::s DIFF t. P x) <=> ?x::s. x NOTIN t /\ P x``,
  simp [RES_EXISTS, CONJ_AC]);

val IN_BIGUNION_RES_EXISTS = store_thm(
  "IN_BIGUNION_RES_EXISTS",
  ``!x sos. x IN BIGUNION sos <=> ?s::sos. x IN s``,
  simp [RES_FORALL, RES_EXISTS, CONJ_AC]);

val RES_EXISTS_BIGUNION = store_thm(
  "RES_EXISTS_BIGUNION",
  ``!P sos. (?x::BIGUNION sos. P x) <=> ?(s::sos) (x::s). P x``,
  simp [RES_EXISTS] >>
  prove_tac []);

val RES_EXISTS_BIGINTER = store_thm(
  "RES_EXISTS_BIGINTER",
  ``!P sos. (?x::BIGINTER sos. P x) <=> ?x. (!s::sos. x IN s) /\ P x``,
  simp [RES_EXISTS, RES_FORALL] >>
  prove_tac []);

(* --------------------------------------------------------------------- *)
(* RES_EXISTS_UNIQUE                                                     *)
(* --------------------------------------------------------------------- *)

(* This one should be called ``RES_EXISTS_UNIQUE``, but the identifier is
already used. *)
val RES_EXISTS_UNIQUE_ELIM = store_thm(
  "RES_EXISTS_UNIQUE_ELIM",
  ``!P s. (?!x::s. P x) <=> ?!x. x IN s /\ P x``,
  rpt gen_tac >>
  simp [RES_EXISTS_UNIQUE, RES_FORALL, RES_EXISTS, EXISTS_UNIQUE_DEF] >>
  prove_tac[]);

val RES_EXISTS_UNIQUE_EXISTS = store_thm(
  "RES_EXISTS_UNIQUE_EXISTS",
  ``!P s. RES_EXISTS_UNIQUE P s ==> RES_EXISTS P s``,
  simp [RES_EXISTS_UNIQUE, RES_EXISTS]);

val RES_EXISTS_UNIQUE_F = store_thm(
  "RES_EXISTS_UNIQUE_F",
  ``!P s x. ~?!x::s. F``,
  simp [RES_EXISTS_UNIQUE_ELIM, EXISTS_UNIQUE_THM]);

val RES_EXISTS_UNIQUE_T = store_thm(
  "RES_EXISTS_UNIQUE_T",
  ``!P s x. (?!x::s. T) <=> ?!x. x IN s``,
  simp [RES_EXISTS_UNIQUE_ELIM]);

val RES_EXISTS_UNIQUE_EMPTY = store_thm
  ("RES_EXISTS_UNIQUE_EMPTY",
   ``!(p : 'a -> bool). ~RES_EXISTS_UNIQUE {} p``,
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_EMPTY, NOT_IN_EMPTY]);

val RES_EXISTS_UNIQUE_NOT_EMPTY = store_thm(
  "RES_EXISTS_UNIQUE_NOT_EMPTY",
  ``!P s. RES_EXISTS_UNIQUE s P ==> (s <> {})``,
  rpt gen_tac >> disch_tac >>
  imp_res_tac RES_EXISTS_UNIQUE_EXISTS >>
  imp_res_tac RES_EXISTS_NOT_EMPTY);

val RES_EXISTS_UNIQUE_UNIV = store_thm
  ("RES_EXISTS_UNIQUE_UNIV",
   ``!(p : 'a -> bool). RES_EXISTS_UNIQUE UNIV p = $?! p``,
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_UNIV, IN_UNIV,
                   RES_FORALL_UNIV, EXISTS_UNIQUE_DEF]
   >> KNOW_TAC ``$? (p:'a->bool) = ?x. p x`` >- RW_TAC bool_ss [ETA_AX]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> PROVE_TAC []);

val RES_EXISTS_UNIQUE_NULL = store_thm
  ("RES_EXISTS_UNIQUE_NULL",
   ``!(p : 'a -> bool) m. RES_EXISTS_UNIQUE p (\x. m) = ((?x. p = {x}) /\ m)``,
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_NULL, NOT_IN_EMPTY,
                   RES_FORALL_NULL, EXISTS_UNIQUE_DEF, EXTENSION, IN_SING]
   >> RW_TAC bool_ss [RES_EXISTS, RES_FORALL]
   >> Cases_on `m`
   >> PROVE_TAC []);

val RES_EXISTS_UNIQUE_SING = store_thm(
  "RES_EXISTS_UNIQUE_SING",
  ``!P s x. (?!x::s. T) <=> ?y. s = {y}``,
  simp [RES_EXISTS_UNIQUE_NULL]);

val RES_EXISTS_UNIQUE_ALT = store_thm
  ("RES_EXISTS_UNIQUE_ALT",
   ``!(p : 'a -> bool) m.
      RES_EXISTS_UNIQUE p m = (?x::p. m x /\ !y::p. m y ==> (y = x))``,
   RW_TAC bool_ss [SPECIFICATION, RES_EXISTS_UNIQUE, RES_EXISTS, RES_FORALL]
   >> PROVE_TAC []);

(* --------------------------------------------------------------------- *)
(* RES_SELECT                                                            *)
(* --------------------------------------------------------------------- *)

val RES_SELECT_EMPTY = store_thm
  ("RES_SELECT_EMPTY",
   ``!(p : 'a -> bool). RES_SELECT {} p = @x. F``,
   RW_TAC bool_ss [RES_SELECT, NOT_IN_EMPTY, ETA_AX]);

val RES_SELECT_UNIV = store_thm
  ("RES_SELECT_UNIV",
   ``!(p : 'a -> bool). RES_SELECT UNIV p = $@ p``,
   RW_TAC bool_ss [RES_SELECT, IN_UNIV, ETA_AX]);

(* --------------------------------------------------------------------- *)
(* RES_ABSTRACT                                                          *)
(* --------------------------------------------------------------------- *)

val RES_ABSTRACT_EQUAL =
  save_thm ("RES_ABSTRACT_EQUAL", CONJUNCT2 RES_ABSTRACT_DEF);

val RES_ABSTRACT_IDEMPOT = store_thm
  ("RES_ABSTRACT_IDEMPOT",
   ``!p m. RES_ABSTRACT p (RES_ABSTRACT p m) = RES_ABSTRACT p m``,
   REPEAT STRIP_TAC
   >> MATCH_MP_TAC RES_ABSTRACT_EQUAL
   >> RW_TAC bool_ss [RES_ABSTRACT]);

(* Sanity check for RES_ABSTRACT definition suggested by Lockwood Morris *)
val RES_ABSTRACT_EQUAL_EQ = store_thm
  ("RES_ABSTRACT_EQUAL_EQ",
   ``!p m1 m2.
      (RES_ABSTRACT p m1 = RES_ABSTRACT p m2) =
      (!x. x IN p ==> (m1 x = m2 x))``,
   REPEAT STRIP_TAC
   >> EQ_TAC >|
   [PROVE_TAC [RES_ABSTRACT],
    PROVE_TAC [RES_ABSTRACT_EQUAL]]);

val RES_ABSTRACT_UNIV = store_thm(
  "RES_ABSTRACT_UNIV",
  ``!m. RES_ABSTRACT UNIV m = m``,
  gen_tac >>
  `!x. RES_ABSTRACT UNIV m x = m x` suffices_by simp [Once FUN_EQ_THM] >>
  simp [RES_ABSTRACT]);

val _ = export_theory();

val _ = let
  val ^^ = Path.concat
  infix ^^
in
  export_theory_as_docfiles (Path.parentArc ^^ "help" ^^ "thms")
end

(* Local Variables: *)
(* fill-column: 78 *)
(* indent-tabs-mode: nil *)
(* End: *)
