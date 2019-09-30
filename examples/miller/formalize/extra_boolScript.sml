(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "extra_bool";
val _ = ParseExtras.temp_loose_equality()

(* interactive mode
show_assums := true;
loadPath := union ["../finished"] (!loadPath);
app load
  ["bossLib", "arithmeticTheory", "dividesTheory", "gcdTheory",
   "primeTheory", "res_quan2Theory", "pred_setTheory", "subtypeTheory",
   "res_quanTools", "subtypeTools", "ho_proverTools", "numContext",
   "millerTools", "extra_numTheory", "ho_basicTools",
   "prob_extraTheory"];
installPP subtypeTools.pp_precontext;
installPP subtypeTools.pp_context;
*)

open bossLib res_quanTheory pred_setTheory subtypeTheory
     res_quanTools subtypeTools ho_proverTools hurdUtils
     ho_basicTools boolContext combinTheory;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS bool_c;

val Strip = S_TAC;
val Simplify = R_TAC;
val Suff = SUFF_TAC;
val Know = KNOW_TAC;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val RAND_THM = store_thm
  ("RAND_THM",
   ``!f x y. (x = y) ==> (f x = f y)``,
   RW_TAC std_ss []);

val K_PARTIAL = store_thm
  ("K_PARTIAL",
   ``!x. K x = \z. x``,
   RW_TAC std_ss [K_DEF]);

val SELECT_EXISTS_UNIQUE = store_thm
  ("SELECT_EXISTS_UNIQUE",
   ``!P n. $? P /\ (!m. P m ==> (m = n)) ==> ($@ P = n)``,
   RW_TAC std_ss [boolTheory.EXISTS_DEF]);

val CONJ_EQ_IMP = store_thm
  ("CONJ_EQ_IMP",
   ``!a b c. (a ==> (b = c)) ==> (a /\ b = a /\ c)``,
   PROVE_TAC []);

(* non-interactive mode
*)
val _ = export_theory ();
