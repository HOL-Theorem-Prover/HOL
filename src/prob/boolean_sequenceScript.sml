(* non-interactive mode
*)
open HolKernel Parse boolLib;

val _ = new_theory "boolean_sequence";

(* interactive mode
if !show_assums then () else
 (load "bossLib";
  load "arithmeticTheory";
  load "probTools";
  load "prob_extraTheory";
  show_assums := true);
*)

open bossLib arithmeticTheory combinTheory
     probTools prob_extraTheory;

infixr 0 ++ || ORELSEC;
infix 1 >>;
nonfix THEN ORELSE;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val SHD_def = Define `SHD (f:num->bool) = f 0`;
val STL_def = Define `STL (f:num->bool) n = f (SUC n)`;
val SCONS_def = Define
  `(SCONS (h:bool) (t:num->bool) 0 = h) /\ (SCONS h t (SUC n) = t n)`;
val SDEST_def = Define `SDEST = \s. (SHD s, STL s)`;

val SCONST_def = Define `SCONST = (K:bool->num->bool)`;

val STAKE_def = Define
  `(STAKE 0 s = []) /\ (STAKE (SUC n) s = SHD s::STAKE n (STL s))`;

val SDROP_def = Define `(SDROP 0 = I) /\ (SDROP (SUC n) = SDROP n o STL)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val SCONS_SURJ = store_thm
  ("SCONS_SURJ",
   Term`!x. ?h t. (x = SCONS h t)`,
   STRIP_TAC
   ++ Q.EXISTS_TAC `SHD x`
   ++ Q.EXISTS_TAC `STL x`
   ++ ONCE_REWRITE_TAC [GSYM EQ_EXT_EQ]
   ++ Cases >> RW_TAC std_ss [SCONS_def, SHD_def]
   ++ RW_TAC std_ss [SCONS_def, STL_def]);

val SHD_STL_ISO = store_thm
  ("SHD_STL_ISO",
   ``!h t. ?x. (SHD x = h) /\ (STL x = t)``,
   REPEAT STRIP_TAC
   ++ Q.EXISTS_TAC `num_case h t`
   ++ RW_TAC arith_ss [SHD_def]
   ++ MATCH_MP_TAC EQ_EXT
   ++ Cases >> RW_TAC std_ss [STL_def]
   ++ RW_TAC std_ss [STL_def]);

val SHD_SCONS = store_thm
  ("SHD_SCONS",
   ``!h t. SHD (SCONS h t) = h``,
   RW_TAC arith_ss [SHD_def, SCONS_def]);

val STL_SCONS = store_thm
  ("STL_SCONS",
   ``!h t. STL (SCONS h t) = t``,
   SUFF_TAC `!h t n. STL (SCONS h t) n = t n` >> PROVE_TAC [EQ_EXT]
   ++ RW_TAC arith_ss [STL_def, SCONS_def]);

val SHD_SCONST = store_thm
  ("SHD_SCONST",
   ``!b. SHD (SCONST b) = b``,
   RW_TAC std_ss [SCONST_def, K_DEF, SHD_def, GSYM EQ_EXT_EQ]);

val STL_SCONST = store_thm
  ("STL_SCONST",
   ``!b. STL (SCONST b) = SCONST b``,
   RW_TAC std_ss [SCONST_def, K_DEF, STL_def, GSYM EQ_EXT_EQ]);

val _ = export_theory ();
