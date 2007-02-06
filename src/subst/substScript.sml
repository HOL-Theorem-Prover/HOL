(* ========================================================================= *)
(* FILE          : substScript.sml                                           *)
(* DESCRIPTION   : Substitution for functions                                *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

open HolKernel boolLib Parse;

val _ = new_theory "subst";

(* ------------------------------------------------------------------------- *)

val _ = set_fixity ":-" (Infix(NONASSOC, 320));

val _ = computeLib.auto_import_definitions := false;

val SUBST_def = TotalDefn.xDefine "SUBST"
  `$:- a b = \f c. if a = c then b else f c`;

val store_thm = Q.store_thm;
val METIS_TAC = metisLib.METIS_TAC;

val SUBST_TAC =
  REPEAT STRIP_TAC
   THEN PURE_REWRITE_TAC [FUN_EQ_THM]
   THEN METIS_TAC [SUBST_def];

val SUBST_EVAL = store_thm("SUBST_EVAL",
  `!f a b c. (a :- b) f c = if a = c then b else f c`, METIS_TAC [SUBST_def]);

val SUBST_NE_COMMUTES = store_thm("SUBST_NE_COMMUTES",
  `!f a b c d. ~(a = b) ==> ((a :- c) ((b :- d) f) = (b :- d) ((a :- c) f))`,
  SUBST_TAC);

val SUBST_EQ = store_thm("SUBST_EQ",
  `!f a b c. (a :- c) ((a :- b) f) = (a :- c) f`, SUBST_TAC);

val SUBST_IMP_ID = store_thm("SUBST_IMP_ID",
  `!f a b. (f a = b) ==> ((a :- b) f = f)`, SUBST_TAC);

val SUBST_ID = store_thm("SUBST_ID",
  `!f a. (a :- f a) f = f`, METIS_TAC [SUBST_IMP_ID]);

(* ------------------------------------------------------------------------- *)

val _ = computeLib.add_persistent_funs [("SUBST_EVAL", SUBST_EVAL)];

val _ = export_theory();
