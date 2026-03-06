(* non-interactive mode
*)
Theory ski
Ancestors
  combin
Libs
  hurdUtils

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

Theorem MK_I:
     (\v. v) = I
Proof
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF, I_THM]
QED

Theorem MK_K:
     !x. (\v. x) = K x
Proof
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF]
QED

Theorem MK_S:
     !x y. (\v. (x v) (y v)) = S x y
Proof
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF]
QED

Theorem MK_o:
     !x y. (\v. x (y v)) = x o y
Proof
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF, o_DEF]
QED

Theorem MK_C:
     !x y. (\v. (x v) y) = C x y
Proof
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF, C_DEF]
QED

Theorem LIFT_K_THRU_S:
     !x y. S (K x) (K y) = K (x y)
Proof
   !! STRIP_TAC
   ++ CONV_TAC (FUN_EQ_CONV)
   ++ RW_TAC std_ss [S_DEF, K_DEF]
QED

(* non-interactive mode
*)
