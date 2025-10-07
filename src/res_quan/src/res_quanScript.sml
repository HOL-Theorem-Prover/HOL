(* res_quanScript.sml - Development of restricted quantifiers

BY: Wai Wong
DATE: 1 Aug 92
CHANGED BY: Joe Hurd, June 2001 (to use predicate sets)
CHANGED BY: Joe Hurd, June 2001 (to remove the ARB from RES_ABSTRACT)
CHANGED BY: Joe Hurd, October 2001 (moved definitions to boolTheory)

============================================================================*)
Theory res_quan
Ancestors
  combin pred_set
Libs
  simpLib pred_setSimps boolSimps BasicProvers


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

Theorem RES_FORALL = RES_FORALL_THM;
Theorem RES_EXISTS = RES_EXISTS_THM;
Theorem RES_EXISTS_UNIQUE = RES_EXISTS_UNIQUE_THM;
Theorem RES_SELECT = RES_SELECT_THM;
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

Theorem RES_FORALL_T:
    !P s x. !x::s. T
Proof
  simp [RES_FORALL_TRUE]
QED

Theorem RES_FORALL_F:
    !P s x. (!x::s. F) <=> (s = {})
Proof
  simp [RES_FORALL, EMPTY]
QED

Theorem RES_FORALL_EMPTY:
     !(p : 'a -> bool). RES_FORALL {} p
Proof
   RW_TAC bool_ss [RES_FORALL, NOT_IN_EMPTY]
QED

Theorem RES_FORALL_UNIV:
     !(p : 'a -> bool). RES_FORALL UNIV p = $! p
Proof
   RW_TAC bool_ss [RES_FORALL, IN_UNIV, ETA_AX]
QED

Theorem RES_FORALL_NULL:
     !(p : 'a -> bool) m. RES_FORALL p (\x. m) = ((p = {}) \/ m)
Proof
   RW_TAC bool_ss [RES_FORALL, EXTENSION, NOT_IN_EMPTY]
   >> Cases_on `m`
   >> PROVE_TAC []
QED

Theorem NOT_RES_FORALL:
    !P s. ~(!x::s. P x) <=> ?x::s. ~P x
Proof
  simp [RES_FORALL, RES_EXISTS]
QED

Theorem RES_FORALL_NOT_EMPTY:
    !P s. ~RES_FORALL s P ==> (s <> {})
Proof
  rpt strip_tac >>
  `RES_FORALL s P` suffices_by (simp []) >>
  pop_assum SUBST1_TAC >>
  MATCH_ACCEPT_TAC RES_FORALL_EMPTY
QED

Theorem RES_FORALL_SUBSET:
    !P s t. s SUBSET t ==> RES_FORALL t P ==> RES_FORALL s P
Proof
  simp [RES_FORALL, SUBSET_DEF]
QED

Theorem RES_FORALL_UNION:
    !P s t. RES_FORALL (s UNION t) P <=> RES_FORALL s P /\ RES_FORALL t P
Proof
  asm_simp_tac (bool_ss ++ DNF_ss ++ PRED_SET_ss) [RES_FORALL]
QED

Theorem RES_FORALL_DIFF:
    !P s t x. (!x::s DIFF t. P x) <=> !x::s. x NOTIN t ==> P x
Proof
  simp [RES_FORALL, AND_IMP_INTRO]
QED

Theorem IN_BIGINTER_RES_FORALL:
    !x sos. x IN BIGINTER sos <=> !s::sos. x IN s
Proof
  simp [RES_FORALL]
QED

Theorem RES_FORALL_BIGUNION:
    !P sos. (!x::BIGUNION sos. P x) <=> !(s::sos) (x::s). P x
Proof
  simp [RES_FORALL, IN_BIGUNION] >>
  prove_tac []
QED

Theorem RES_FORALL_BIGINTER:
    !P sos. (!x::BIGINTER sos. P x) <=> !x. (!s::sos. x IN s) ==> P x
Proof
  simp [RES_FORALL]
QED

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

Theorem RES_EXISTS_F:
    !P s x. ~?s::x. F
Proof
  simp [RES_EXISTS_FALSE]
QED

Theorem RES_EXISTS_T:
    !P s x. (?x::s. T) <=> (s <> {})
Proof
  simp [RES_EXISTS, EMPTY]
QED

Theorem RES_EXISTS_EMPTY:
     !(p : 'a -> bool). ~RES_EXISTS {} p
Proof
   RW_TAC bool_ss [RES_EXISTS, NOT_IN_EMPTY]
QED

Theorem RES_EXISTS_UNIV:
     !(p : 'a -> bool). RES_EXISTS UNIV p = $? p
Proof
   RW_TAC bool_ss [RES_EXISTS, IN_UNIV, ETA_AX]
QED

Theorem RES_EXISTS_NULL:
     !(p : 'a -> bool) m. RES_EXISTS p (\x. m) = (~(p = {}) /\ m)
Proof
   RW_TAC bool_ss [RES_EXISTS, EXTENSION, NOT_IN_EMPTY]
   >> Cases_on `m`
   >> PROVE_TAC []
QED

Theorem RES_EXISTS_ALT:
  !(p : 'a -> bool) m.
      RES_EXISTS p m <=> (RES_SELECT p m) IN p /\ m (RES_SELECT p m)
Proof
   RW_TAC bool_ss [RES_EXISTS, EXISTS_DEF, RES_SELECT, SPECIFICATION]
QED

Theorem NOT_RES_EXISTS:
    !P s. ~(?x::s. P x) <=> !x::s. ~P x
Proof
  simp [RES_FORALL, RES_EXISTS, GSYM IMP_DISJ_THM]
QED

Theorem RES_EXISTS_NOT_EMPTY:
    !P s. RES_EXISTS s P ==> (s <> {})
Proof
  rpt strip_tac >>
  `~RES_EXISTS s P` suffices_by simp [] >>
  pop_assum SUBST1_TAC >>
  MATCH_ACCEPT_TAC RES_EXISTS_EMPTY
QED

Theorem RES_EXISTS_SUBSET:
    !P s t. s SUBSET t ==> RES_EXISTS s P ==> RES_EXISTS t P
Proof
  simp [RES_EXISTS, SUBSET_DEF] >>
  prove_tac []
QED

Theorem RES_EXISTS_UNION:
    !P s t. RES_EXISTS (s UNION t) P <=> RES_EXISTS s P \/ RES_EXISTS t P
Proof
  simp [RES_EXISTS] >>
  prove_tac []
QED

Theorem RES_EXISTS_DIFF:
    !P s t x. (?x::s DIFF t. P x) <=> ?x::s. x NOTIN t /\ P x
Proof
  simp [RES_EXISTS, CONJ_AC]
QED

Theorem IN_BIGUNION_RES_EXISTS:
    !x sos. x IN BIGUNION sos <=> ?s::sos. x IN s
Proof
  simp [RES_FORALL, RES_EXISTS, CONJ_AC]
QED

Theorem RES_EXISTS_BIGUNION:
    !P sos. (?x::BIGUNION sos. P x) <=> ?(s::sos) (x::s). P x
Proof
  simp [RES_EXISTS] >>
  prove_tac []
QED

Theorem RES_EXISTS_BIGINTER:
    !P sos. (?x::BIGINTER sos. P x) <=> ?x. (!s::sos. x IN s) /\ P x
Proof
  simp [RES_EXISTS, RES_FORALL] >>
  prove_tac []
QED

(* --------------------------------------------------------------------- *)
(* RES_EXISTS_UNIQUE                                                     *)
(* --------------------------------------------------------------------- *)

(* This one should be called ``RES_EXISTS_UNIQUE``, but the identifier is
already used. *)
Theorem RES_EXISTS_UNIQUE_ELIM:
    !P s. (?!x::s. P x) <=> ?!x. x IN s /\ P x
Proof
  rpt gen_tac >>
  simp [RES_EXISTS_UNIQUE, RES_FORALL, RES_EXISTS, EXISTS_UNIQUE_DEF] >>
  prove_tac[]
QED

Theorem RES_EXISTS_UNIQUE_EXISTS:
    !P s. RES_EXISTS_UNIQUE P s ==> RES_EXISTS P s
Proof
  simp [RES_EXISTS_UNIQUE, RES_EXISTS]
QED

Theorem RES_EXISTS_UNIQUE_F:
    !P s x. ~?!x::s. F
Proof
  simp [RES_EXISTS_UNIQUE_ELIM, EXISTS_UNIQUE_THM]
QED

Theorem RES_EXISTS_UNIQUE_T:
    !P s x. (?!x::s. T) <=> ?!x. x IN s
Proof
  simp [RES_EXISTS_UNIQUE_ELIM]
QED

Theorem RES_EXISTS_UNIQUE_EMPTY:
     !(p : 'a -> bool). ~RES_EXISTS_UNIQUE {} p
Proof
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_EMPTY, NOT_IN_EMPTY]
QED

Theorem RES_EXISTS_UNIQUE_NOT_EMPTY:
    !P s. RES_EXISTS_UNIQUE s P ==> (s <> {})
Proof
  rpt gen_tac >> disch_tac >>
  imp_res_tac RES_EXISTS_UNIQUE_EXISTS >>
  imp_res_tac RES_EXISTS_NOT_EMPTY
QED

Theorem RES_EXISTS_UNIQUE_UNIV:
     !(p : 'a -> bool). RES_EXISTS_UNIQUE UNIV p = $?! p
Proof
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_UNIV, IN_UNIV,
                   RES_FORALL_UNIV, EXISTS_UNIQUE_DEF]
   >> KNOW_TAC ``$? (p:'a->bool) = ?x. p x`` >- RW_TAC bool_ss [ETA_AX]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> PROVE_TAC []
QED

Theorem RES_EXISTS_UNIQUE_NULL:
     !(p : 'a -> bool) m. RES_EXISTS_UNIQUE p (\x. m) = ((?x. p = {x}) /\ m)
Proof
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_NULL, NOT_IN_EMPTY,
                   RES_FORALL_NULL, EXISTS_UNIQUE_DEF, EXTENSION, IN_SING]
   >> RW_TAC bool_ss [RES_EXISTS, RES_FORALL]
   >> Cases_on `m`
   >> PROVE_TAC []
QED

Theorem RES_EXISTS_UNIQUE_SING:
    !P s x. (?!x::s. T) <=> ?y. s = {y}
Proof
  simp [RES_EXISTS_UNIQUE_NULL]
QED

Theorem RES_EXISTS_UNIQUE_ALT:
     !(p : 'a -> bool) m.
      RES_EXISTS_UNIQUE p m = (?x::p. m x /\ !y::p. m y ==> (y = x))
Proof
   RW_TAC bool_ss [SPECIFICATION, RES_EXISTS_UNIQUE, RES_EXISTS, RES_FORALL]
   >> PROVE_TAC []
QED

(* --------------------------------------------------------------------- *)
(* RES_SELECT                                                            *)
(* --------------------------------------------------------------------- *)

Theorem RES_SELECT_EMPTY:
     !(p : 'a -> bool). RES_SELECT {} p = @x. F
Proof
   RW_TAC bool_ss [RES_SELECT, NOT_IN_EMPTY, ETA_AX]
QED

Theorem RES_SELECT_UNIV:
     !(p : 'a -> bool). RES_SELECT UNIV p = $@ p
Proof
   RW_TAC bool_ss [RES_SELECT, IN_UNIV, ETA_AX]
QED

(* --------------------------------------------------------------------- *)
(* RES_ABSTRACT                                                          *)
(* --------------------------------------------------------------------- *)

Theorem RES_ABSTRACT_EQUAL = CONJUNCT2 RES_ABSTRACT_DEF;

Theorem RES_ABSTRACT_IDEMPOT:
     !p m. RES_ABSTRACT p (RES_ABSTRACT p m) = RES_ABSTRACT p m
Proof
   REPEAT STRIP_TAC
   >> MATCH_MP_TAC RES_ABSTRACT_EQUAL
   >> RW_TAC bool_ss [RES_ABSTRACT]
QED

(* Sanity check for RES_ABSTRACT definition suggested by Lockwood Morris *)
Theorem RES_ABSTRACT_EQUAL_EQ:
     !p m1 m2.
      (RES_ABSTRACT p m1 = RES_ABSTRACT p m2) =
      (!x. x IN p ==> (m1 x = m2 x))
Proof
   REPEAT STRIP_TAC
   >> EQ_TAC >|
   [PROVE_TAC [RES_ABSTRACT],
    PROVE_TAC [RES_ABSTRACT_EQUAL]]
QED

Theorem RES_ABSTRACT_UNIV:
    !m. RES_ABSTRACT UNIV m = m
Proof
  gen_tac >>
  `!x. RES_ABSTRACT UNIV m x = m x` suffices_by simp [Once FUN_EQ_THM] >>
  simp [RES_ABSTRACT]
QED

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
