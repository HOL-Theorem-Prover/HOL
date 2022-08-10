(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "ski";

(* interactive mode
val () = loadPath := union ["..", "../finished"] (!loadPath);
val () = app load
  ["bossLib",
   "pred_setTheory",
   "realLib",
   "pairTheory",
   "combinTheory",
   "res_quanLib",
   "dividesTheory",
   "primeTheory",
   "gcdTheory",
   "prob_extraTools",
   "hoTools"];
val () = show_assums := true;
*)

open bossLib combinTheory hurdUtils;

infixr 0 ++ << || THENC ORELSEC ORELSER ## |->;
infix 1 >>;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val op!! = op REPEAT;

val _ = Parse.reveal "C";

(* ------------------------------------------------------------------------- *)
(* ski theorems.                                                             *)
(* ------------------------------------------------------------------------- *)

val MK_I = store_thm
  ("MK_I",
   ``(\v. v) = I``,
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF, I_THM]);

val MK_K = store_thm
  ("MK_K",
   ``!x. (\v. x) = K x``,
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF]);

val MK_S = store_thm
  ("MK_S",
   ``!x y. (\v. (x v) (y v)) = S x y``,
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF]);

val MK_o = store_thm
  ("MK_o",
   ``!x y. (\v. x (y v)) = x o y``,
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF, o_DEF]);

val MK_C = store_thm
  ("MK_C",
   ``!x y. (\v. (x v) y) = C x y``,
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF, C_DEF]);

val LIFT_K_THRU_S = store_thm
  ("LIFT_K_THRU_S",
   ``!x y. S (K x) (K y) = K (x y)``,
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF]);

(* non-interactive mode
*)
val _ = export_theory ();
