(* ========================================================================= *)
(* Create "posrealTheory" for reasoning about non-negative real numbers      *)
(* extended with a positive infinity.                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
val () = app load
 ["bossLib", "metisLib", "arithmeticTheory", "realLib", "posetTheory"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib;
open combinTheory optionTheory arithmeticTheory realTheory realLib;
open posetTheory;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "posreal"                                       *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "posreal";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;

(* ------------------------------------------------------------------------- *)
(* An uninterpreted constant.                                                *)
(* ------------------------------------------------------------------------- *)

val unint_def = Define `unint x = x`;

(* ------------------------------------------------------------------------- *)
(* A HOL type of positive reals                                              *)
(* ------------------------------------------------------------------------- *)

val posreal_pred_def = Define
  `(posreal_pred NONE = T) /\ (posreal_pred (SOME x) <=> 0r <= x)`;

val posreal_inhabited =
  prove (``?x. posreal_pred x``, METIS_TAC [posreal_pred_def]);

val posreal_tydef = new_type_definition ("posreal", posreal_inhabited);

val posreal_tybij = define_new_type_bijections
  {name = "posreal_tybij", ABS = "posreal_abs",
   REP = "posreal_rep", tyax = posreal_tydef};

val posreal_cancel = store_thm
  ("posreal_cancel",
   ``(posreal_rep (posreal_abs NONE) = NONE) /\
     !x. 0 <= x ==> (posreal_rep (posreal_abs (SOME x)) = SOME x)``,
   METIS_TAC [posreal_tybij, posreal_pred_def]);

val posreal_abs_inj = store_thm
  ("posreal_abs_inj",
   ``!x y.
       posreal_pred x /\ posreal_pred y /\ (posreal_abs x = posreal_abs y) ==>
       (x = y)``,
   METIS_TAC [posreal_tybij]);

(* ------------------------------------------------------------------------- *)
(* Defining the extended arithmetic operations                               *)
(* ------------------------------------------------------------------------- *)

val preal_addr_def = Define
  `(preal_addr NONE NONE = NONE) /\
   (preal_addr NONE (SOME y) = NONE) /\
   (preal_addr (SOME x) NONE = NONE) /\
   (preal_addr (SOME (x:real)) (SOME y) = SOME (x + y))`;

val preal_subr_def = Define
  `(preal_subr NONE (SOME y) = NONE) /\
   (preal_subr (SOME x) NONE = (SOME 0r)) /\
   (preal_subr (SOME (x:real)) (SOME y) = SOME (if x <= y then 0 else x - y))`;

val preal_ler_def = Define
  `(preal_ler NONE NONE = T) /\
   (preal_ler NONE (SOME y) = F) /\
   (preal_ler (SOME x) NONE = T) /\
   (preal_ler (SOME (x:real)) (SOME y) <=> x <= y)`;

val preal_mulr_def = Define
  `(preal_mulr NONE NONE = NONE) /\
   (preal_mulr NONE (SOME y) = if y = 0r then SOME 0 else NONE) /\
   (preal_mulr (SOME x) NONE = if x = 0 then SOME 0 else NONE) /\
   (preal_mulr (SOME x) (SOME y) = SOME (x * y))`;

val preal_invr_def = Define
  `(preal_invr NONE = SOME 0r) /\
   (preal_invr (SOME x) = if x = 0 then NONE else SOME (inv x))`;

(* ------------------------------------------------------------------------- *)
(* Defining the arithmetic operations on the posreal type                    *)
(* ------------------------------------------------------------------------- *)

val preal_def = Define `preal x = posreal_abs (SOME (pos x))`;

val infty_def = Define `infty = posreal_abs NONE`;

val posreal_of_num_def = Define `posreal_of_num n = preal (& n)`;

val preal_add_def = Define
  `preal_add x y = posreal_abs (preal_addr (posreal_rep x) (posreal_rep y))`;

val preal_sub_def = Define
  `preal_sub x y = posreal_abs (preal_subr (posreal_rep x) (posreal_rep y))`;

val preal_le_def = Define
  `preal_le x y = preal_ler (posreal_rep x) (posreal_rep y)`;

val preal_lt_def = Define `preal_lt x y = ~preal_le y x`;

val preal_mul_def = Define
  `preal_mul x y = posreal_abs (preal_mulr (posreal_rep x) (posreal_rep y))`;

val preal_inv_def = Define
  `preal_inv x = posreal_abs (preal_invr (posreal_rep x))`;

val preal_div_def = Define `preal_div x y = preal_mul x (preal_inv y)`;

val _ = add_numeral_form (#"p", SOME "posreal_of_num");
val _ = overload_on ("+",   Term `preal_add`);
val _ = overload_on ("-",   Term `preal_sub`);
val _ = overload_on ("*",   Term `preal_mul`);
val _ = overload_on ("/",   Term `preal_div`);
val _ = overload_on ("<=",  Term `preal_le`);
val _ = overload_on ("<",   Term `preal_lt`);
val _ = overload_on ("inv", Term `preal_inv`);

(* ------------------------------------------------------------------------- *)
(* A useful case split                                                       *)
(* ------------------------------------------------------------------------- *)

val posreal_cases = store_thm
  ("posreal_cases",
   ``!x. (x = infty) \/ ?y. 0 <= y /\ (x = preal y)``,
   RW_TAC std_ss [preal_def, infty_def]
   >> MP_TAC (Q.SPEC `x` (CONJUNCT1 posreal_tybij))
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [SYM th])
   >> Cases_on `posreal_rep x` >- RW_TAC std_ss []
   >> DISJ2_TAC
   >> METIS_TAC [posreal_pred_def, posreal_tybij, pos_def]);

val posreal_trich = store_thm
  ("posreal_trich",
   ``!x.
       (x = 0) \/ (x = infty) \/
       ~(x = 0) /\ ?y. ~(y = 0) /\ 0 <= y /\ (x = preal y)``,
   GEN_TAC
   >> Cases_on `x = 0` >- RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `x` posreal_cases)
   >> RW_TAC std_ss []
   >> DISJ2_TAC
   >> Q.EXISTS_TAC `y`
   >> RW_TAC std_ss []
   >> METIS_TAC [posreal_of_num_def]);

local
  val posreal = Type `:posreal`;

  fun pcase_split x =
    STRIP_ASSUME_TAC (SPEC x posreal_cases)
    THEN POP_ASSUM (fn th => FULL_SIMP_TAC boolSimps.bool_ss [th]);

  fun pcase3_split x =
    STRIP_ASSUME_TAC (SPEC x posreal_trich)
    THEN POP_ASSUM (fn th => FULL_SIMP_TAC boolSimps.bool_ss [th]);
in
  fun pcases goal =
    let val v = genvar posreal in X_GEN_TAC v THEN pcase_split v end goal;

  val pcases_on = Q_TAC pcase_split;

  fun pcases3 goal =
    let val v = genvar posreal in X_GEN_TAC v THEN pcase3_split v end goal;

  val pcases3_on = Q_TAC pcase3_split;
end;

(* ------------------------------------------------------------------------- *)
(* Theorems about arithmetic                                                 *)
(* ------------------------------------------------------------------------- *)

val preal_inj = store_thm
  ("preal_inj",
   ``!x y. 0 <= x /\ 0 <= y /\ (preal x = preal y) ==> (x = y)``,
   RW_TAC std_ss [preal_def]
   >> Suff `pos x = pos y` >- RW_TAC real_ss [pos_def]
   >> ONCE_REWRITE_TAC [GSYM SOME_11]
   >> MATCH_MP_TAC posreal_abs_inj
   >> RW_TAC std_ss [posreal_pred_def, REAL_POS_POS]);

val preal_eq_zero = store_thm
  ("preal_eq_zero",
   ``!x. (preal x = 0) <=> x <= 0``,
   RW_TAC std_ss [preal_def, posreal_of_num_def]
   >> REVERSE EQ_TAC >- METIS_TAC [REAL_POS_EQ_ZERO, pos_def, REAL_LE_REFL]
   >> STRIP_TAC
   >> Know `pos x = pos 0`
   >- METIS_TAC
      [posreal_abs_inj, posreal_pred_def, REAL_POS_POS, optionTheory.SOME_11]
   >> SIMP_TAC real_ss [Q.SPEC `0` pos_def]);

val posreal_of_num_inj = store_thm
  ("posreal_of_num_inj",
   ``!m n. (posreal_of_num m = posreal_of_num n) = (m = n)``,
   RW_TAC std_ss [posreal_of_num_def]
   >> REVERSE EQ_TAC >- RW_TAC std_ss []
   >> STRIP_TAC
   >> Suff `(& m : real) = & n` >- RW_TAC real_ss []
   >> MATCH_MP_TAC preal_inj
   >> RW_TAC real_ss []);

val preal_add = store_thm
  ("preal_add",
   ``!x y. 0 <= x /\ 0 <= y ==> (preal x + preal y = preal (x + y))``,
   RW_TAC std_ss [preal_add_def, preal_def, posreal_cancel, REAL_POS_POS]
   >> RW_TAC std_ss [preal_addr_def, pos_def]
   >> Suff `F` >- REWRITE_TAC []
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val posreal_of_num_add = store_thm
  ("posreal_of_num_add",
   ``!m n. posreal_of_num m + posreal_of_num n = posreal_of_num (m + n)``,
   RW_TAC real_ss [posreal_of_num_def, preal_add]);

val preal_sub = store_thm
  ("preal_sub",
   ``!x y. 0 <= y ==> (preal x - preal y = preal (x - y))``,
   RW_TAC std_ss [preal_sub_def, preal_def, posreal_cancel, REAL_POS_POS]
   >> RW_TAC real_ss [preal_subr_def, pos_def, REAL_LE_SUB_LADD]
   >| [Suff `x = y` >- RW_TAC real_ss []
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC,
       Suff `x = y` >- RW_TAC real_ss []
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC,
       Suff `x = 0` >- RW_TAC real_ss []
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC,
       Suff `y = 0` >- RW_TAC real_ss []
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC]);

val posreal_of_num_sub = store_thm
  ("posreal_of_num_sub",
   ``!a b. posreal_of_num a - posreal_of_num b = posreal_of_num (a - b)``,
   RW_TAC std_ss [posreal_of_num_def, preal_sub, REAL_POS, REAL_SUB]
   >> RW_TAC std_ss
      [GSYM posreal_of_num_def, preal_eq_zero, REAL_NEG_LE0, REAL_POS,
       DECIDE ``(a:num) <= b ==> (a - b = 0)``]);

val preal_le = store_thm
  ("preal_le",
   ``!x y. x <= y ==> preal x <= preal y``,
   RW_TAC std_ss [preal_def]
   >> RW_TAC std_ss [preal_le_def, posreal_cancel, preal_ler_def, REAL_POS_POS]
   >> METIS_TAC [REAL_POS_MONO]);

val preal_mul = store_thm
  ("preal_mul",
   ``!x y. 0 <= x \/ 0 <= y ==> (preal x * preal y = preal (x * y))``,
   RW_TAC real_ss
   [preal_mul_def, preal_mulr_def, posreal_cancel, preal_def, REAL_POS_POS,
    pos_def]
   >| [METIS_TAC [REAL_LE_MUL],
       Suff `x = 0` >- RW_TAC real_ss []
       >> Suff `~(~(x = 0) /\ 0 < x)`
       >- (REPEAT (POP_ASSUM MP_TAC) >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `~(0 <= y)` MP_TAC
       >> Suff `~(y = 0) ==> 0 < y` >- REAL_ARITH_TAC
       >> STRIP_TAC
       >> MP_TAC (Q.SPECL [`x`, `y`] (GSYM REAL_LT_LMUL_0))
       >> RW_TAC std_ss [REAL_LT_LE]
       >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
       >> RW_TAC std_ss [REAL_ENTIRE],
       Suff `y = 0` >- RW_TAC real_ss []
       >> Suff `~(~(y = 0) /\ 0 < y)`
       >- (REPEAT (POP_ASSUM MP_TAC) >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `~(0 <= x)` MP_TAC
       >> Suff `~(x = 0) ==> 0 < x` >- REAL_ARITH_TAC
       >> STRIP_TAC
       >> MP_TAC (Q.SPECL [`x`, `y`] (GSYM REAL_LT_RMUL_0))
       >> RW_TAC std_ss [REAL_LT_LE]
       >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
       >> RW_TAC std_ss [REAL_ENTIRE]]);

val posreal_of_num_mul = store_thm
  ("posreal_of_num_mul",
   ``!m n. posreal_of_num m * posreal_of_num n = posreal_of_num (m * n)``,
   RW_TAC real_ss [posreal_of_num_def, preal_mul]);

val le_preal = store_thm
  ("le_preal",
   ``!x y. 0 <= y /\ preal x <= preal y ==> x <= y``,
   RW_TAC std_ss [preal_def]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss
      [preal_le_def, posreal_cancel, preal_ler_def, REAL_POS_POS, pos_def]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val preal_not_infty = store_thm
  ("preal_not_infty",
   ``!x. ~(preal x = infty)``,
   RW_TAC std_ss [preal_def, infty_def]
   >> METIS_TAC [REAL_POS_POS, posreal_pred_def, posreal_tybij, NOT_SOME_NONE]);

val posreal_of_num_not_infty = store_thm
  ("posreal_of_num_not_infty",
   ``!n. ~(posreal_of_num n = infty)``,
   RW_TAC std_ss [posreal_of_num_def, preal_not_infty]);

val le_refl = store_thm
  ("le_refl",
   ``!x. x <= x``,
   pcases
   >> RW_TAC real_ss
      [infty_def, preal_def, preal_le_def, posreal_cancel, preal_ler_def]);

val le_infty = store_thm
  ("le_infty",
   ``!x. x <= infty``,
   pcases
   >> RW_TAC real_ss
      [infty_def, preal_le_def, preal_def, posreal_cancel, preal_ler_def]);

val infty_le = store_thm
  ("infty_le",
   ``!x. infty <= x <=> (x = infty)``,
   pcases
   >> RW_TAC real_ss [le_refl, preal_not_infty]
   >> RW_TAC real_ss
      [infty_def, preal_le_def, preal_def, posreal_cancel, preal_ler_def]);

val zero_le = store_thm
  ("zero_le",
   ``!x. 0 <= x``,
   pcases
   >> RW_TAC real_ss
      [preal_le_def, preal_def, posreal_of_num_def, posreal_cancel, infty_def,
       preal_ler_def, REAL_POS_POS]
   >> METIS_TAC [REAL_POS_MONO]);

val le_zero = store_thm
  ("le_zero",
   ``!x. x <= 0 <=> (x = 0)``,
   pcases >- (RW_TAC real_ss [infty_le] >> PROVE_TAC [])
   >> RW_TAC real_ss
      [preal_le_def, preal_def, posreal_of_num_def, posreal_cancel,
       preal_ler_def, REAL_POS_POS]
   >> RW_TAC std_ss [pos_def]
   >> Know `y <= 0 <=> (y = 0)` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> DISCH_THEN (fn th => REWRITE_TAC [th])
   >> EQ_TAC >- RW_TAC std_ss []
   >> METIS_TAC [posreal_abs_inj, posreal_pred_def, REAL_LE_REFL, SOME_11]);

val le_antisym = store_thm
  ("le_antisym",
   ``!x y. x <= y /\ y <= x ==> (x = y)``,
   pcases
   >> pcases
   >> RW_TAC std_ss [infty_le, le_infty, preal_not_infty]
   >> PROVE_TAC [le_preal, REAL_LE_ANTISYM]);

val le_trans = store_thm
  ("le_trans",
   ``!x y z. x <= y /\ y <= z ==> x <= z``,
   REPEAT pcases
   >> RW_TAC real_ss [infty_le, le_refl, le_infty]
   >> METIS_TAC [preal_le, le_preal, REAL_LE_TRANS, infty_le, preal_not_infty]);

val le_total = store_thm
  ("le_total",
   ``!x y. x <= y \/ y <= x``,
   (REPEAT pcases >> RW_TAC std_ss [le_infty, infty_le])
   >> PROVE_TAC [le_preal, preal_le, REAL_LE_TOTAL]);

val add_comm = store_thm
  ("add_comm",
   ``!x y. x + y = y + x``,
   REPEAT pcases
   >> RW_TAC std_ss
      [preal_add_def, preal_addr_def, posreal_cancel, infty_def,
       preal_def, REAL_POS_POS]
   >> METIS_TAC [REAL_ADD_SYM]);

val add_assoc = store_thm
  ("add_assoc",
   ``!x y z. x + y + z = x + (y + z)``,
   REPEAT pcases
   >> RW_TAC real_ss
      [infty_def, preal_def, posreal_cancel, preal_add_def, preal_addr_def,
       REAL_LE_ADD]
   >> METIS_TAC [REAL_ADD_ASSOC]);

val infty_ladd = store_thm
  ("infty_ladd",
   ``!x. infty + x = infty``,
   pcases
   >> RW_TAC std_ss
      [preal_add_def, preal_addr_def, posreal_cancel, infty_def,
       preal_def, REAL_POS_POS]);

val infty_radd = store_thm
  ("infty_radd",
   ``!x. x + infty = infty``,
   METIS_TAC [infty_ladd, add_comm]);

val le_add2 = store_thm
  ("le_add2",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> x1 + x2 <= y1 + y2``,
   REPEAT pcases
   >> RW_TAC std_ss
      [preal_add, infty_ladd, infty_radd, infty_le, le_infty, preal_not_infty]
   >> METIS_TAC [preal_le, le_preal, REAL_LE_ADD2]);

val sub_sub2 = store_thm
  ("sub_sub2",
   ``!x y. y <= x /\ ~(x = infty) ==> (x - (x - y) = y)``,
   pcases
   >> pcases >- RW_TAC std_ss [infty_le, preal_not_infty]
   >> RW_TAC std_ss [preal_not_infty]
   >> Know `y' <= y` >- METIS_TAC [le_preal]
   >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC std_ss [preal_sub]
   >> Suff `0 <= y - y' /\ y - y' <= y` >- RW_TAC real_ss [preal_sub]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val le_sub_ladd = store_thm
  ("le_sub_ladd",
   ``!x y z. z <= y /\ y ≠ infty ==> (x <= y - z <=> x + z <= y)``,
   (REPEAT pcases >> RW_TAC std_ss [le_infty, infty_le, infty_ladd])
   >- METIS_TAC [preal_not_infty, le_preal, preal_sub]
   >> Know `y'' <= y'` >- METIS_TAC [le_preal]
   >> RW_TAC std_ss [preal_sub, preal_add]
   >> Suff `0 <= y' - y''` >- METIS_TAC [preal_le, le_preal, REAL_LE_SUB_LADD]
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

val sub_decrease = store_thm
  ("sub_decrease",
   ``!x y. ~(x = infty) \/ ~(y = infty) ==> (x - y <= x)``,
   (REPEAT pcases >> RW_TAC std_ss [le_infty, infty_le, preal_not_infty])
   >> RW_TAC real_ss
      [preal_le_def, preal_def, preal_ler_def, posreal_cancel, REAL_POS_POS,
       infty_def, preal_sub_def, preal_subr_def]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [pos_def]
   >> Know `0 <= y - y'` >- (REPEAT (POP_ASSUM MP_TAC) >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [posreal_cancel, preal_ler_def]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val sub_linfty = store_thm
  ("sub_linfty",
   ``!x. ~(x = infty) ==> (infty - x = infty)``,
   pcases
   >> RW_TAC std_ss
      [preal_sub_def, infty_def, preal_def, posreal_cancel, preal_subr_def,
       REAL_POS_POS]);

val sub_rinfty = store_thm
  ("sub_rinfty",
   ``!x. ~(x = infty) ==> (x - infty = 0)``,
   pcases
   >> RW_TAC std_ss
      [preal_sub_def, infty_def, preal_def, posreal_cancel, preal_subr_def,
       REAL_POS_POS, posreal_of_num_def, pos_def]);

val sub_mono = store_thm
  ("sub_mono",
   ``!x y z. ~(z = infty) /\ x <= y ==> x - z <= y - z``,
   REPEAT pcases
   >> RW_TAC std_ss [preal_sub, sub_linfty, infty_le, preal_not_infty, le_infty]
   >> MATCH_MP_TAC preal_le
   >> RW_TAC real_ss []
   >> METIS_TAC [le_preal]);

val le_epsilon = store_thm
  ("le_epsilon",
   ``!x y. (!e. ~(e = 0) ==> x <= y + e) ==> x <= y``,
   (REPEAT pcases >> RW_TAC std_ss [le_infty, infty_le])
   >- (POP_ASSUM MP_TAC
       >> RW_TAC std_ss [preal_not_infty]
       >> Q.EXISTS_TAC `1`
       >> CONJ_TAC >- RW_TAC arith_ss [posreal_of_num_inj]
       >> RW_TAC real_ss [posreal_of_num_def, preal_add, preal_not_infty])
   >> MATCH_MP_TAC preal_le
   >> MATCH_MP_TAC REAL_LE_EPSILON
   >> RW_TAC std_ss [REAL_LT_LE]
   >> Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `preal e`)
   >> MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
   >> CONJ_TAC
   >- (RW_TAC std_ss [posreal_of_num_def]
       >> METIS_TAC [preal_inj, REAL_LE_REFL])
   >> RW_TAC std_ss [preal_add]
   >> METIS_TAC [le_preal, REAL_LE_ADD]);

val let_trans = store_thm
  ("let_trans",
   ``!x y z. x <= y /\ y < z ==> x < z``,
   RW_TAC std_ss [preal_lt_def]
   >> METIS_TAC [le_trans, le_total]);

val lte_trans = store_thm
  ("lte_trans",
   ``!x y z. x < y /\ y <= z ==> x < z``,
   RW_TAC std_ss [preal_lt_def]
   >> METIS_TAC [le_trans, le_total]);

val lt_le = store_thm
  ("lt_le",
   ``!x y. x < y ==> x <= y``,
   RW_TAC std_ss [preal_lt_def]
   >> METIS_TAC [le_total]);

val posreal_of_num_le = store_thm
  ("posreal_of_num_le",
   ``!m n. posreal_of_num m <= posreal_of_num n <=> m <= n``,
   RW_TAC std_ss [posreal_of_num_def]
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC `real_of_num m <= real_of_num n`
   >> REVERSE CONJ_TAC >- RW_TAC real_ss []
   >> METIS_TAC [le_preal, preal_le, REAL_POS]);

val posreal_of_num_lt = store_thm
  ("posreal_of_num_lt",
   ``!m n. posreal_of_num m < posreal_of_num n <=> m < n``,
   METIS_TAC
   [posreal_of_num_le, preal_lt_def, arithmeticTheory.NOT_LESS_EQUAL]);

val add_rinfty = store_thm
  ("add_rinfty",
   ``!x. x + infty = infty``,
   pcases
   >> RW_TAC std_ss
      [posreal_cancel, preal_add_def, preal_addr_def, REAL_POS_POS,
       infty_def, preal_def]);

val add_linfty = store_thm
  ("add_linfty",
   ``!x. infty + x = infty``,
   METIS_TAC [add_comm, add_rinfty]);

val add_rzero = store_thm
  ("add_rzero",
   ``!x. x + 0 = x``,
   pcases
   >> RW_TAC std_ss
      [posreal_cancel, preal_add_def, preal_addr_def, REAL_POS_POS,
       infty_def, preal_def, posreal_of_num_def]
   >> RW_TAC real_ss [pos_def]);

val add_lzero = store_thm
  ("add_lzero",
   ``!x. 0 + x = x``,
   METIS_TAC [add_comm, add_rzero]);

val le_ladd = store_thm
  ("le_ladd",
   ``!x y z. x + y <= x + z <=> x = infty \/ y <= z``,
   RW_TAC std_ss []
   >> REVERSE EQ_TAC >- METIS_TAC [le_add2, le_refl, add_linfty]
   >> pcases_on `x`
   >> SIMP_TAC std_ss [preal_not_infty]
   >> pcases_on `z` >- RW_TAC std_ss [le_infty]
   >> pcases_on `y`
   >- RW_TAC std_ss [add_rinfty, infty_le, preal_add, preal_not_infty]
   >> RW_TAC std_ss [preal_add]
   >> METIS_TAC [preal_le, le_preal, REAL_LE_ADD, REAL_LE_LADD]);

val le_radd = store_thm
  ("le_radd",
   ``!x y z. y + x <= z + x <=> x = infty \/ y <= z``,
   METIS_TAC [le_ladd, add_comm]);

val addl_le = store_thm
  ("addl_le",
   ``!x y. x + y <= y <=> x = 0 \/ (y = infty)``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`y`, `x`, `0`] le_radd)
   >> METIS_TAC [le_zero, add_lzero]);

val addr_le = store_thm
  ("addr_le",
   ``!x y. y + x <= y <=> x = 0 \/ y = infty``,
   METIS_TAC [addl_le, add_comm]);

val le_addl = store_thm
  ("le_addl",
   ``!x y. y <= x + y``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`y`, `0`, `x`] le_radd)
   >> RW_TAC std_ss [add_lzero, zero_le]);

val le_addr = store_thm
  ("le_addr",
   ``!x y. y <= y + x``,
   METIS_TAC [le_addl, add_comm]);

val lt_addr = store_thm
  ("lt_addr",
   ``!x y. y < y + x <=> x ≠ 0 /\ y ≠ infty``,
   METIS_TAC [addr_le, preal_lt_def]);

val lt_addl = store_thm
  ("lt_addl",
   ``!x y. y < x + y <=> ~(x = 0) /\ ~(y = infty)``,
   METIS_TAC [lt_addr, add_comm]);

val addr_lt = store_thm
  ("addr_lt",
   ``!x y. ~(y + x < y)``,
   METIS_TAC [le_addr, preal_lt_def]);

val addl_lt = store_thm
  ("addl_lt",
   ``!x y. ~(x + y < y)``,
   METIS_TAC [addr_lt, add_comm]);

val sub_le_imp = store_thm
  ("sub_le_imp",
   ``!x y z. (~(x = infty) \/ ~(y = infty)) /\ y <= z + x ==> y - x <= z``,
   REPEAT pcases
   >> RW_TAC std_ss
      [le_infty, infty_le, sub_linfty, sub_rinfty, zero_le, preal_not_infty,
       preal_add, preal_sub]
   >> METIS_TAC [preal_le, le_preal, REAL_LE_SUB_RADD, REAL_LE_ADD]);

val le_sub_imp = store_thm
  ("le_sub_imp",
   ``!x y z. (~(x = infty) \/ ~(z = infty)) /\ y + x <= z ==> y <= z - x``,
   REPEAT pcases
   >> RW_TAC std_ss
      [le_infty, infty_le, sub_linfty, sub_rinfty, zero_le, preal_not_infty,
       preal_add, preal_sub, le_zero, add_linfty, add_rinfty]
   >> METIS_TAC [preal_le, le_preal, REAL_LE_SUB_LADD, REAL_LE_ADD]);

val lt_sub_imp = store_thm
  ("lt_sub_imp",
   ``!x y z. (~(x = infty) \/ ~(z = infty)) /\ y + x < z ==> y < z - x``,
   REPEAT pcases
   >> RW_TAC std_ss
      [le_infty, infty_le, sub_linfty, sub_rinfty, zero_le, preal_not_infty,
       preal_add, preal_sub, preal_lt_def, add_rinfty, add_linfty]
   >> METIS_TAC [preal_le, le_preal, REAL_LE_SUB_RADD, REAL_LE_ADD]);

val sub_lt_imp = store_thm
  ("sub_lt_imp",
   ``!x y z.
       z ≠ 0 /\ (x ≠ infty \/ y ≠ infty) /\ y < z + x ==>
       y - x < z``,
   (REPEAT pcases
    >> RW_TAC std_ss
       [le_infty, infty_le, sub_linfty, sub_rinfty, zero_le, preal_not_infty,
        preal_add, preal_sub, le_zero, add_linfty, add_rinfty, preal_lt_def,
        posreal_of_num_def])
   >- (STRIP_TAC
       >> Q.PAT_X_ASSUM `~X` MP_TAC
       >> Suff `y' = 0` >- RW_TAC std_ss []
       >> ASM_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
       >> METIS_TAC [le_preal, REAL_LE_REFL])
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `~X` MP_TAC
   >> REWRITE_TAC []
   >> MATCH_MP_TAC preal_le
   >> RW_TAC std_ss [GSYM REAL_LE_SUB_LADD]
   >> Suff `0 <= y' - y` >- METIS_TAC [le_preal]
   >> CCONTR_TAC
   >> Q.PAT_X_ASSUM `~(X = Y)` MP_TAC
   >> REWRITE_TAC []
   >> MATCH_MP_TAC le_antisym
   >> REVERSE CONJ_TAC >- RW_TAC std_ss [GSYM posreal_of_num_def, zero_le]
   >> Q.PAT_X_ASSUM `X <= Y` MP_TAC
   >> RW_TAC std_ss [preal_def, pos_def]);

Theorem preal_le_eq0:
   !x y. 0 <= x /\ 0 <= y ==> (preal x <= preal y <=> x <= y)
Proof
  METIS_TAC [preal_le, le_preal]
QED

val preal_lt_eq = store_thm
  ("preal_lt_eq",
   ``!x y. 0 <= x /\ 0 <= y ==> (preal x < preal y <=> x < y)``,
   METIS_TAC [preal_lt_def, real_lt, preal_le_eq0]);

val sub_lzero = store_thm
  ("sub_lzero",
   ``!x. 0 - x = 0``,
   pcases
   >> RW_TAC real_ss
      [posreal_of_num_def, preal_def, infty_def, preal_sub_def,
       posreal_cancel, REAL_POS_POS, preal_subr_def]
   >> FULL_SIMP_TAC real_ss [pos_def]
   >> PROVE_TAC []);

val sub_rzero = store_thm
  ("sub_rzero",
   ``!x. x - 0 = x``,
   pcases
   >> RW_TAC real_ss
      [posreal_of_num_def, preal_def, infty_def, preal_sub_def,
       posreal_cancel, REAL_POS_POS, preal_subr_def]
   >> FULL_SIMP_TAC real_ss [pos_def]
   >> PROVE_TAC [REAL_LE_ANTISYM]);

val le_imp_sub_zero = store_thm
  ("le_imp_sub_zero",
   ``!x y. (~(x = infty) \/ ~(y = infty)) /\ x <= y ==> (x - y = 0)``,
   RW_TAC real_ss [GSYM le_zero]
   >> MATCH_MP_TAC sub_le_imp
   >> METIS_TAC [add_lzero]);

val sub_zero_imp_le = store_thm
  ("sub_zero_imp_le",
   ``!x y. (~(x = infty) \/ ~(y = infty)) /\ (x - y = 0) ==> x <= y``,
   REPEAT pcases
   >> RW_TAC real_ss
      [le_infty, infty_le, sub_linfty, preal_not_infty,
       posreal_of_num_not_infty, preal_sub]
   >> MATCH_MP_TAC preal_le
   >> Suff `y - y' <= 0` >- REAL_ARITH_TAC
   >> Suff `pos (y - y') = 0` >- RW_TAC real_ss []
   >> FULL_SIMP_TAC std_ss [preal_def, posreal_of_num_def]
   >> METIS_TAC
      [posreal_abs_inj, posreal_pred_def, REAL_POS_POS, pos_def, REAL_LE_REFL,
       optionTheory.SOME_11]);

val sub_add2 = store_thm
  ("sub_add2",
   ``!x y. x <= y /\ ~(x = infty) ==> (x + (y - x) = y)``,
   REPEAT pcases
   >> RW_TAC real_ss
      [le_infty, infty_le, sub_linfty, preal_not_infty,
       posreal_of_num_not_infty, preal_sub, add_rinfty]
   >> Know `0 <= y' - y`
   >- (Suff `y <= y'` >- REAL_ARITH_TAC >> METIS_TAC [le_preal])
   >> STRIP_TAC
   >> RW_TAC real_ss [preal_add]);

Theorem preal_add_eq:
  !x y.
    preal x + preal y =
    if 0 <= x then if 0 <= y then preal (x + y) else preal x else preal y
Proof
   RW_TAC real_ss [preal_add]
   >> RW_TAC real_ss [preal_def, pos_def]
   >> (Know `0r <= 0` >- RW_TAC real_ss [])
   >> STRIP_TAC
   >> IMP_RES_TAC (GSYM REAL_POS_ID)
   >> ASSUM_LIST ONCE_REWRITE_TAC
   >> SIMP_TAC std_ss
      [GSYM preal_def, GSYM posreal_of_num_def, add_rzero, add_lzero]
QED

val preal_sub_eq = store_thm
  ("preal_sub_eq",
   ``!x y. preal x - preal y = if 0 <= y then preal (x - y) else preal x``,
   RW_TAC real_ss [preal_sub]
   >> RW_TAC real_ss [preal_def]
   >> MP_TAC (Q.SPEC `y` pos_def)
   >> DISCH_THEN (fn th => SIMP_TAC real_ss [th])
   >> RW_TAC std_ss []
   >> Know `0 = pos 0` >- RW_TAC real_ss [pos_def]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> RW_TAC std_ss [GSYM preal_def, GSYM posreal_of_num_def, sub_rzero]);

val preal_inj_eq = store_thm
  ("preal_inj_eq",
   ``!x y. (preal x = preal y) = if x <= 0 then y <= 0 else x = y``,
   RW_TAC real_ss [preal_def]
   >> REVERSE EQ_TAC >- METIS_TAC [REAL_POS_EQ_ZERO]
   >> STRIP_TAC
   >> (Know `pos x = pos y`
   >- METIS_TAC
      [posreal_abs_inj, posreal_pred_def, REAL_POS_POS, optionTheory.SOME_11])
   >> POP_ASSUM (K ALL_TAC)
   >> METIS_TAC [REAL_POS_EQ_ZERO, pos_def]);

val preal_le_eq = store_thm
  ("preal_le_eq",
   ``!x y. preal x <= preal y <=> if 0 <= y then x <= y else x <= 0``,
   RW_TAC real_ss [] >- METIS_TAC [preal_le, le_preal]
   >> Know `y <= 0` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [GSYM preal_eq_zero, le_zero]);

Theorem posreal_of_num_sub[allow_rebind]:
  !m n : num. & m - & n = & (m - n)
Proof
  RW_TAC real_ss [posreal_of_num_def, preal_sub]
  >> RW_TAC real_ss [preal_def]
  >> Suff `pos (& m - & n) = pos (& (m - n))` >- RW_TAC std_ss []
  >> REVERSE (Cases_on `0r <= & m - & n`)
  >- (RW_TAC real_ss [pos_def]
      >> Suff `(& m : real) <= & n` >- RW_TAC real_ss []
      >> POP_ASSUM MP_TAC
      >> REAL_ARITH_TAC)
  >> RW_TAC real_ss [pos_def, REAL_EQ_SUB_RADD]
  >> Suff `n <= m` >- DECIDE_TAC
  >> Suff `(& n : real) <= & m` >- RW_TAC real_ss []
  >> POP_ASSUM MP_TAC
  >> REAL_ARITH_TAC
QED

val le_antisym_eq = store_thm
  ("le_antisym_eq",
   ``!x y. x = y ⇔ x <= y /\ y <= x``,
   METIS_TAC [le_antisym, le_refl]);

val add_sub = store_thm
  ("add_sub",
   ``!x y. ~(y = infty) ==> (x + y - y = x)``,
   REPEAT pcases
   >> RW_TAC real_ss
      [preal_addr_def, preal_add_def, preal_subr_def, preal_sub_def,
       posreal_cancel, preal_not_infty, preal_def, infty_def, REAL_LE_ADD,
       pos_def]
   >> METIS_TAC [REAL_LE_ANTISYM, REAL_ADD_LID, REAL_LE_RADD]);

val add_sub2 = store_thm
  ("add_sub2",
   ``!x y. ~(y = infty) ==> (y + x - y = x)``,
   METIS_TAC [add_sub, add_comm]);

val sub_add = store_thm
  ("sub_add",
   ``!x y. y <= x /\ ~(y = infty) ==> ((x - y) + y = x)``,
   METIS_TAC [sub_add2, add_comm]);

val le_sub_eq = store_thm
  ("le_sub_eq",
   ``!x y z.
       (~(y = 0) /\ (~(x = infty) \/ ~(z = infty))) ==>
       (y <= z - x <=> y + x <= z)``,
   METIS_TAC [le_sub_imp, sub_lt_imp, preal_lt_def]);

val sub_le_eq = store_thm
  ("sub_le_eq",
   ``!x y z. (~(x = infty) \/ ~(y = infty)) ==> (y - x <= z ⇔ y <= z + x)``,
   METIS_TAC [sub_le_imp, lt_sub_imp, preal_lt_def]);

val le_eq_sub_zero = store_thm
  ("le_eq_sub_zero",
   ``!x y. x <= y ⇔ (y = infty) \/ (x - y = 0)``,
   METIS_TAC [le_imp_sub_zero, sub_zero_imp_le, le_infty]);

val mul_comm = store_thm
  ("mul_comm",
   ``!x y. x * y = y * x``,
   REPEAT pcases
   >> RW_TAC std_ss
      [preal_mul_def, preal_mulr_def, posreal_cancel, infty_def, preal_def,
       REAL_POS_POS, posreal_of_num_def, pos_def]
   >> METIS_TAC [REAL_MUL_SYM]);

val mul_assoc = store_thm
  ("mul_assoc",
   ``!x y z. x * y * z = x * (y * z)``,
   REPEAT pcases
   >> RW_TAC real_ss
      [infty_def, preal_def, posreal_cancel, preal_mul_def, preal_mulr_def,
       REAL_LE_MUL]
   >> METIS_TAC
      [REAL_LE_ANTISYM, REAL_MUL_LZERO, pos_def, REAL_LE_REFL, REAL_ENTIRE,
       REAL_MUL_ASSOC]);

val mul_lzero = store_thm
  ("mul_lzero",
   ``!x. 0 * x = 0``,
   pcases
   >> RW_TAC std_ss
      [preal_mul_def, preal_mulr_def, posreal_cancel, infty_def, preal_def,
       REAL_POS_POS, posreal_of_num_def]
   >> FULL_SIMP_TAC real_ss [pos_def]);

val mul_rzero = store_thm
  ("mul_rzero",
   ``!x. x * 0 = 0``,
   METIS_TAC [mul_lzero, mul_comm]);

val mul_linfty = store_thm
  ("mul_linfty",
   ``!x. infty * x = if x = 0 then 0 else infty``,
   RW_TAC std_ss [mul_rzero]
   >> pcases_on `x`
   >> RW_TAC std_ss
      [preal_mul_def, preal_mulr_def, posreal_cancel, infty_def, preal_def,
       REAL_POS_POS, posreal_of_num_def, pos_def]
   >> FULL_SIMP_TAC std_ss [posreal_of_num_def]);

val mul_rinfty = store_thm
  ("mul_rinfty",
   ``!x. x * infty = if x = 0 then 0 else infty``,
   METIS_TAC [mul_linfty, mul_comm]);

val mul_lone = store_thm
  ("mul_lone",
   ``!x. 1 * x = x``,
   pcases
   >> RW_TAC real_ss
      [posreal_of_num_def, preal_def, infty_def, preal_mul_def,
       posreal_cancel, REAL_POS_POS, preal_mulr_def]
   >> RW_TAC real_ss [pos_def]);

val mul_rone = store_thm
  ("mul_rone",
   ``!x. x * 1 = x``,
   METIS_TAC [mul_lone, mul_comm]);

val entire = store_thm
  ("entire",
   ``!x y. x * y = 0 <=> x = 0 \/ y = 0``,
   REPEAT pcases3
   >> RW_TAC std_ss
      [mul_lzero, mul_rzero, mul_linfty, posreal_of_num_not_infty, mul_rinfty,
       preal_mul]
   >> RW_TAC std_ss [posreal_of_num_def]
   >> METIS_TAC [preal_inj, REAL_ENTIRE, REAL_LE_REFL, REAL_LE_MUL]);

val le_mul2 = store_thm
  ("le_mul2",
   ``!x1 y1 x2 y2. x1 <= y1 /\ x2 <= y2 ==> x1 * x2 <= y1 * y2``,
   REPEAT pcases
   >> RW_TAC real_ss
      [infty_def, preal_def, preal_mul_def, preal_mulr_def, preal_le_def,
       preal_ler_def, posreal_cancel, pos_def, REAL_LE_MUL]
   >> METIS_TAC
      [real_lt, REAL_LT_LE, REAL_MUL_RZERO, REAL_LE_ANTISYM, REAL_MUL_LZERO,
       REAL_LE_MUL2]);

val le_lmul_imp = store_thm
  ("le_lmul_imp",
   ``!x y z. y <= z ==> x * y <= x * z``,
   METIS_TAC [le_mul2, le_refl]);

val le_rmul_imp = store_thm
  ("le_rmul_imp",
   ``!x y z. y <= z ==> y * x <= z * x``,
   METIS_TAC [le_lmul_imp, mul_comm]);

Theorem mul_eq_infty:
  !x y.
    (x * y = infty) <=> (x = infty) /\ ~(y = 0) \/ ~(x = 0) /\ (y = infty)
Proof
   pcases3
   >> pcases3
   >> RW_TAC std_ss [mul_linfty, mul_rinfty, mul_lzero, mul_rzero,
                     posreal_of_num_not_infty, preal_mul, preal_not_infty]
QED

val add_ldistrib = store_thm
  ("add_ldistrib",
   ``!x y z. x * (y + z) = x * y + x * z``,
   REPEAT pcases3
   >> RW_TAC real_ss
      [REAL_LE_ADD, REAL_LE_MUL, preal_mul, preal_add, mul_linfty,
       posreal_of_num_not_infty, add_linfty, add_rinfty, mul_rinfty,
       mul_lzero, add_lzero, mul_rzero, add_rzero, REAL_LDISTRIB]
   >> Suff `~(preal (y + y') = 0)` >- RW_TAC real_ss [mul_linfty]
   >> RW_TAC real_ss [preal_eq_zero]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val add_rdistrib = store_thm
  ("add_rdistrib",
   ``!x y z. (y + z) * x = y * x + z * x``,
   METIS_TAC [add_ldistrib, mul_comm]);

val sub_ldistrib = store_thm
  ("sub_ldistrib",
   ``!x y z.
       ~(x = infty) /\ (~(y = infty) \/ ~(z = infty)) ==>
       (x * (y - z) = x * y - x * z)``,
   RW_TAC std_ss []
   >> REVERSE (Cases_on `z <= y`)
   >- (Know `y - z = 0` >- METIS_TAC [le_imp_sub_zero, le_total]
       >> RW_TAC std_ss [mul_rzero]
       >> METIS_TAC [le_total, le_imp_sub_zero, le_lmul_imp, mul_eq_infty])
   >> MATCH_MP_TAC le_antisym
   >> (CONJ_TAC
       >| [MATCH_MP_TAC le_sub_imp
           >> RW_TAC std_ss [mul_eq_infty, GSYM add_ldistrib]
           >> METIS_TAC [sub_add, infty_le, le_refl],
           MATCH_MP_TAC sub_le_imp
           >> RW_TAC std_ss [mul_eq_infty, GSYM add_ldistrib]
           >> METIS_TAC [sub_add, infty_le, le_refl]]));

val sub_rdistrib = store_thm
  ("sub_rdistrib",
   ``!x y z.
       ~(x = infty) /\ (~(y = infty) \/ ~(z = infty)) ==>
       ((y - z) * x = y * x - z * x)``,
   METIS_TAC [sub_ldistrib, mul_comm]);

val mul_swap = store_thm
  ("mul_swap",
   ``!x y z. x * (y * z) = y * (x * z)``,
   METIS_TAC [mul_comm, mul_assoc]);

val double = store_thm
  ("double",
   ``!x. 2 * x = x + x``,
   Know `2 = 1 + 1` >- RW_TAC arith_ss [posreal_of_num_add, posreal_of_num_inj]
   >> RW_TAC std_ss [add_rdistrib, mul_lone]);

val inv_zero = store_thm
  ("inv_zero",
   ``inv 0 = infty``,
   RW_TAC real_ss
   [posreal_of_num_def, preal_def, infty_def, preal_inv_def,
    posreal_cancel, REAL_POS_POS, preal_invr_def]);

val inv_infty = store_thm
  ("inv_infty",
   ``inv infty = 0``,
   RW_TAC real_ss
   [posreal_of_num_def, preal_def, infty_def, preal_inv_def,
    posreal_cancel, REAL_POS_POS, preal_invr_def]
   >> RW_TAC real_ss [pos_def]);

val inv_one = store_thm
  ("inv_one",
   ``inv 1 = 1``,
   RW_TAC real_ss
   [posreal_of_num_def, preal_def, infty_def, preal_inv_def,
    posreal_cancel, REAL_POS_POS, preal_invr_def]
   >> RW_TAC real_ss [pos_def, REAL_INV1]);

val preal_inv = store_thm
  ("preal_inv",
   ``!x. 0 <= x ==> (inv (preal x) = if x = 0 then infty else preal (inv x))``,
   RW_TAC real_ss
   [posreal_of_num_def, preal_def, infty_def, preal_inv_def,
    posreal_cancel, REAL_POS_POS, preal_invr_def]
   >| [METIS_TAC [REAL_LE_ANTISYM],
       METIS_TAC [REAL_LE_REFL],
       RW_TAC real_ss [pos_def, REAL_LE_INV]]);

Theorem inv_antimono:
  !x y. inv x <= inv y <=> y <= x
Proof
   (REPEAT pcases3
    >> RW_TAC std_ss
       [inv_zero, inv_infty, le_infty, zero_le, le_zero, preal_not_infty,
        posreal_of_num_inj, infty_le, posreal_of_num_not_infty, preal_inv])
   >- (RW_TAC real_ss [posreal_of_num_def]
       >> METIS_TAC
          [preal_inj, REAL_LE_INV, REAL_INV_EQ_0, pos_def, REAL_LE_REFL])
   >> Suff `~(inv y <= inv y') = ~(y' <= y)`
   >- METIS_TAC [le_preal, preal_le, REAL_LE_INV]
   >> PURE_REWRITE_TAC [GSYM real_lt]
   >> MATCH_MP_TAC REAL_INV_LT_ANTIMONO
   >> REPEAT (Q.PAT_X_ASSUM `~(preal X = Y)` (K ALL_TAC))
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC
QED

val inv_one_le = store_thm
  ("inv_one_le",
   ``!x. 1 <= inv x <=> x <= 1``,
   ONCE_REWRITE_TAC [GSYM inv_one]
   >> RW_TAC std_ss [inv_antimono]
   >> RW_TAC std_ss [inv_one]);

val inv_le_one = store_thm
  ("inv_le_one",
   ``!x. inv x <= 1 <=> 1 <= x``,
   ONCE_REWRITE_TAC [GSYM inv_one]
   >> RW_TAC std_ss [inv_antimono]
   >> RW_TAC std_ss [inv_one]);

val inv_inv = store_thm
  ("inv_inv",
   ``!x. inv (inv x) = x``,
   pcases3
   >> RW_TAC std_ss [preal_not_infty, inv_zero, inv_infty]
   >> RW_TAC real_ss
      [preal_inv_def, infty_def, preal_def, posreal_cancel, preal_invr_def,
       pos_def, REAL_LE_INV]
   >> METIS_TAC
      [REAL_INV_EQ_0, posreal_abs_inj, posreal_pred_def, REAL_LE_INV,
       optionTheory.SOME_11, REAL_INV_INV]);

val inv_inj = store_thm
  ("inv_inj",
   ``!x y. (inv x = inv y) = (x = y)``,
   METIS_TAC [inv_inv]);

val inv_eq_zero = store_thm
  ("inv_eq_zero",
   ``!x. (inv x = 0) = (x = infty)``,
   METIS_TAC [inv_inj, inv_infty]);

val inv_eq_one = store_thm
  ("inv_eq_one",
   ``!x. (inv x = 1) = (x = 1)``,
   METIS_TAC [inv_inj, inv_one]);

val inv_eq_infty = store_thm
  ("inv_eq_infty",
   ``!x. (inv x = infty) = (x = 0)``,
   METIS_TAC [inv_inj, inv_zero]);

val mul_linv = store_thm
  ("mul_linv",
   ``!x. ~(x = 0) /\ ~(x = infty) ==> (inv x * x = 1)``,
   pcases3
   >> RW_TAC std_ss [preal_not_infty]
   >> RW_TAC real_ss
      [preal_inv_def, preal_mul_def, preal_def, preal_mulr_def,
       preal_invr_def, posreal_cancel, posreal_of_num_def, REAL_LE_INV,
       pos_def, REAL_MUL_LINV]);

val mul_rinv = store_thm
  ("mul_rinv",
   ``!x. ~(x = 0) /\ ~(x = infty) ==> (x * inv x = 1)``,
   METIS_TAC [mul_linv, mul_comm]);

val mul_rinv2 = store_thm
  ("mul_rinv2",
   ``!x y. ~(x = 0) /\ ~(x = infty) ==> (x * (inv x * y) = y)``,
   RW_TAC std_ss [GSYM mul_assoc, mul_rinv, mul_lone]);

val inv_mul = store_thm
  ("inv_mul",
   ``!a b. inv (a * b) = if a * b = 0 then infty else inv a * inv b``,
   pcases3
   >> pcases3
   >> RW_TAC std_ss
      [mul_linfty, mul_rinfty, mul_lzero, mul_rzero, inv_zero,
       posreal_of_num_not_infty, inv_infty, preal_mul]
   >> Know `0 <= y * y' /\ ~(y * y' = 0)`
   >- METIS_TAC [REAL_ENTIRE, REAL_LE_MUL]
   >> RW_TAC std_ss [preal_inv, REAL_INV_MUL, REAL_LE_INV, preal_mul]);

val half_between = store_thm
  ("half_between",
   ``(0 < 1/2 /\ 1/2 < 1) /\ (0 <= 1/2 /\ 1/2 <= 1)``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   >> CONJ_TAC >- PROVE_TAC [lt_le]
   >> SIMP_TAC arith_ss
      [preal_div_def, mul_lone, preal_lt_def, le_zero, inv_eq_zero,
       posreal_of_num_not_infty, inv_one_le, posreal_of_num_le]);

val thirds_between = store_thm
  ("thirds_between",
   ``((0p < 1/3 /\ 1/3 < 1p) /\ (0p < 2/3 /\ 2/3 < 1p)) /\
     ((0p <= 1/3 /\ 1/3 <= 1p) /\ (0p <= 2/3 /\ 2/3 <= 1p))``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   >> CONJ_TAC >- PROVE_TAC [lt_le]
   >> RW_TAC real_ss
      [posreal_of_num_def, preal_lt_eq, preal_div_def, preal_mul, preal_inv,
       REAL_LE_INV, REAL_LE_MUL]
   >> RW_TAC std_ss [GSYM real_div]
   >> RW_TAC std_ss [REAL_INV_1OVER, REAL_THIRDS_BETWEEN]);

val preal_div = store_thm
  ("preal_div",
   ``!a b.
       0 <= a /\ 0 <= b ==>
       (preal a / preal b =
        if a = 0 then 0 else if b = 0 then infty else preal (a / b))``,
   RW_TAC std_ss
   [preal_div_def, preal_inv, mul_lzero, GSYM posreal_of_num_def,
    preal_mul, real_div, REAL_MUL_LZERO, mul_rinfty]
   >> RW_TAC real_ss [posreal_of_num_def]
   >> METIS_TAC [preal_inj]);

val div_lzero = store_thm
  ("div_lzero",
   ``!x. 0 / x = 0``,
   RW_TAC std_ss [preal_div_def, mul_lzero]);

val div_rzero = store_thm
  ("div_rzero",
   ``!x. x / 0 = if x = 0 then 0 else infty``,
   RW_TAC std_ss [preal_div_def, mul_rinfty, inv_zero, mul_lzero]);

val div_lone = store_thm
  ("div_lone",
   ``!x. 1 / x = inv x``,
   RW_TAC std_ss [preal_div_def, mul_lone]);

val div_rone = store_thm
  ("div_rone",
   ``!x. x / 1 = x``,
   RW_TAC std_ss [preal_div_def, mul_rone, inv_one]);

val div_linfty = store_thm
  ("div_linfty",
   ``!x. infty / x = if x = infty then 0 else infty``,
   RW_TAC std_ss
   [preal_div_def, mul_linfty, inv_infty, mul_rzero, inv_eq_zero]);

val div_rinfty = store_thm
  ("div_rinfty",
   ``!x. x / infty = 0``,
   RW_TAC std_ss [preal_div_def, mul_rzero, inv_infty]);

val div_eq_zero = store_thm
  ("div_eq_zero",
   ``!x y. (x / y = 0) <=> (x = 0) \/ (y = infty)``,
   RW_TAC std_ss [preal_div_def, entire, inv_eq_zero]);

val div_eq_infty = store_thm
  ("div_eq_infty",
   ``!x y.
       (x / y = infty) <=>
       ~(x = 0) /\ (y = 0) \/
       (x = infty) /\ ~(y = infty)``,
   RW_TAC std_ss [preal_div_def, mul_eq_infty, inv_eq_zero, inv_eq_infty]
   >> METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(* Minimum and maximum                                                       *)
(* ------------------------------------------------------------------------- *)

val preal_min_def = Define
  `preal_min (x : posreal) y = if x <= y then x else y`;

val preal_max_def = Define
  `preal_max (x : posreal) y = if x <= y then y else x`;

val _ = overload_on ("min", Term `preal_min`);
val _ = overload_on ("max", Term `preal_max`);

val min_le = store_thm
  ("min_le",
   ``!z x y. min x y <= z <=> x <= z \/ y <= z``,
   RW_TAC std_ss [preal_min_def]
   >> PROVE_TAC [le_total, le_trans]);

val min_le1 = store_thm
  ("min_le1",
   ``!x y. min x y <= x``,
   PROVE_TAC [min_le, le_refl]);

val min_le2 = store_thm
  ("min_le2",
   ``!x y. min x y <= y``,
   PROVE_TAC [min_le, le_refl]);

val le_min = store_thm
  ("le_min",
   ``!z x y. z <= min x y <=> z <= x /\ z <= y``,
   RW_TAC std_ss [preal_min_def]
   >> PROVE_TAC [le_total, le_trans]);

val min_le2_imp = store_thm
  ("min_le2_imp",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> min x1 x2 <= min y1 y2``,
   RW_TAC std_ss [le_min]
   >> RW_TAC std_ss [min_le]);

val min_refl = store_thm
  ("min_refl",
   ``!x. min x x = x``,
   RW_TAC std_ss [preal_min_def, le_refl]);

val min_le_lin = store_thm
  ("min_le_lin",
   ``!z x y. min x y <= z * x + (1 - z) * y``,
   RW_TAC std_ss [preal_min_def]
   >| [MATCH_MP_TAC le_trans
       >> Cases_on `1 <= z`
       >- (Q.EXISTS_TAC `z * x`
           >> RW_TAC std_ss [le_addr]
           >> METIS_TAC [le_rmul_imp, mul_lone])
       >> Q.EXISTS_TAC `z * x + (1 - z) * x`
       >> REVERSE CONJ_TAC >- RW_TAC std_ss [le_ladd, le_lmul_imp]
       >> RW_TAC std_ss [GSYM add_rdistrib]
       >> Know `z <= 1` >- METIS_TAC [le_total]
       >> STRIP_TAC
       >> Know `~(z = infty)` >- METIS_TAC [infty_le, posreal_of_num_not_infty]
       >> RW_TAC std_ss [sub_add2, mul_lone, le_refl],
       Know `y <= x` >- METIS_TAC [le_total]
       >> STRIP_TAC
       >> MATCH_MP_TAC le_trans
       >> Q.EXISTS_TAC `z * y + (1 - z) * y`
       >> REVERSE CONJ_TAC >- RW_TAC std_ss [le_radd, le_lmul_imp]
       >> REVERSE (Cases_on `z <= 1`)
       >- (MATCH_MP_TAC le_trans
           >> Q.EXISTS_TAC `z * y`
           >> RW_TAC std_ss [le_addr]
           >> METIS_TAC [le_rmul_imp, mul_lone, le_total])
       >> RW_TAC std_ss [GSYM add_rdistrib]
       >> Know `~(z = infty)` >- METIS_TAC [infty_le, posreal_of_num_not_infty]
       >> RW_TAC std_ss [sub_add2, mul_lone, le_refl]]);

val min_comm = store_thm
  ("min_comm",
   ``!x y. min x y = min y x``,
   RW_TAC std_ss [preal_min_def]
   >> PROVE_TAC [le_antisym, le_total]);

val min_rinfty = store_thm
  ("min_rinfty",
   ``!x : posreal. min x infty = x``,
   RW_TAC std_ss [preal_min_def, le_infty]);

val min_linfty = store_thm
  ("min_linfty",
   ``!x : posreal. min infty x = x``,
   PROVE_TAC [min_rinfty, min_comm]);

val min_lzero = store_thm
  ("min_lzero",
   ``!x : posreal. min 0 x = 0``,
   RW_TAC std_ss [preal_min_def, zero_le]);

val min_rzero = store_thm
  ("min_rzero",
   ``!x : posreal. min x 0 = 0``,
   PROVE_TAC [min_lzero, min_comm]);

val le_max = store_thm
  ("le_max",
   ``!z x y. z <= max x y <=> z <= x \/ z <= y``,
   RW_TAC std_ss [preal_max_def]
   >> PROVE_TAC [le_total, le_trans]);

val le_max1 = store_thm
  ("le_max1",
   ``!x y. x <= max x y``,
   PROVE_TAC [le_max, le_refl]);

val le_max2 = store_thm
  ("le_max2",
   ``!x y. y <= max x y``,
   PROVE_TAC [le_max, le_refl]);

val max_le = store_thm
  ("max_le",
   ``!z x y. max x y <= z <=> x <= z /\ y <= z``,
   RW_TAC std_ss [preal_max_def]
   >> PROVE_TAC [le_total, le_trans]);

val max_le2_imp = store_thm
  ("max_le2_imp",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> max x1 x2 <= max y1 y2``,
   RW_TAC std_ss [max_le]
   >> RW_TAC std_ss [le_max]);

val max_refl = store_thm
  ("max_refl",
   ``!x. max x x = x``,
   RW_TAC std_ss [preal_max_def, le_refl]);

val lin_le_max = store_thm
  ("lin_le_max",
   ``!z x y. z <= 1 ==> z * x + (1 - z) * y <= max x y``,
   RW_TAC std_ss [preal_max_def]
   >| [MATCH_MP_TAC le_trans
       >> Q.EXISTS_TAC `z * y + (1 - z) * y`
       >> CONJ_TAC >- RW_TAC std_ss [le_radd, le_lmul_imp]
       >> RW_TAC std_ss [GSYM add_rdistrib]
       >> Know `~(z = infty)` >- METIS_TAC [infty_le, posreal_of_num_not_infty]
       >> RW_TAC std_ss [sub_add2, mul_lone, le_refl],
       Know `y <= x` >- METIS_TAC [le_total]
       >> STRIP_TAC
       >> MATCH_MP_TAC le_trans
       >> Q.EXISTS_TAC `z * x + (1 - z) * x`
       >> CONJ_TAC >- RW_TAC std_ss [le_ladd, le_lmul_imp]
       >> RW_TAC std_ss [GSYM add_rdistrib]
       >> Know `~(z = infty)` >- METIS_TAC [infty_le, posreal_of_num_not_infty]
       >> RW_TAC std_ss [sub_add2, mul_lone, le_refl]]);

val max_comm = store_thm
  ("max_comm",
   ``!x y. max x y = max y x``,
   RW_TAC std_ss [preal_max_def]
   >> PROVE_TAC [le_antisym, le_total]);

val max_rinfty = store_thm
  ("max_rinfty",
   ``!x : posreal. max x infty = infty``,
   RW_TAC std_ss [preal_max_def, le_infty]);

val max_linfty = store_thm
  ("max_linfty",
   ``!x : posreal. max infty x = infty``,
   PROVE_TAC [max_rinfty, max_comm]);

val max_lzero = store_thm
  ("max_lzero",
   ``!x : posreal. max 0 x = x``,
   RW_TAC std_ss [preal_max_def, zero_le]);

val max_rzero = store_thm
  ("max_rzero",
   ``!x : posreal. max x 0 = x``,
   PROVE_TAC [max_lzero, max_comm]);

(* ------------------------------------------------------------------------- *)
(* 1-boundedness                                                             *)
(* ------------------------------------------------------------------------- *)

val bound1_def = Define `bound1 (x:posreal) = if x <= 1 then x else 1`;

val bound1 = store_thm
  ("bound1",
   ``!x. bound1 x <= 1``,
   RW_TAC std_ss [bound1_def, le_refl]);

val bound1_basic = store_thm
  ("bound1_basic",
   ``(bound1 0 = 0) /\ (bound1 1 = 1) /\ (bound1 (1 / 2) = 1 / 2) /\
     (bound1 (1 / 3) = 1 / 3) /\ (bound1 (2 / 3) = 2 / 3)``,
   RW_TAC std_ss [bound1_def, zero_le, half_between, thirds_between]);

val bound1_cancel = store_thm
  ("bound1_cancel",
   ``!x. bound1 x + (1 - bound1 x) = 1``,
   GEN_TAC
   >> MATCH_MP_TAC sub_add2
   >> RW_TAC std_ss [bound1]
   >> METIS_TAC [posreal_of_num_not_infty, infty_le, le_trans, bound1]);

val bound1_cancel2 = store_thm
  ("bound1_cancel2",
   ``!x. (1 - bound1 x) + bound1 x = 1``,
   METIS_TAC [bound1_cancel, add_comm]);

val bound1_min = store_thm
  ("bound1_min",
   ``!x. bound1 x = min x 1``,
   RW_TAC std_ss [bound1_def, preal_min_def]);

val bound1_infty = store_thm
  ("bound1_infty",
   ``bound1 infty = 1``,
   RW_TAC std_ss [bound1_min, min_linfty]);

(* ------------------------------------------------------------------------- *)
(* Supremums and infimums (these are always defined on posreals)             *)
(* ------------------------------------------------------------------------- *)

val preal_sup_def = Define
  `preal_sup p =
   if !x. (!y. p y ==> y <= x) ==> (x = infty) then infty
   else preal (sup (\r. (r = 0) \/ (0 <= r /\ p (preal r))))`;

val preal_inf_def = Define
  `preal_inf p =
   if !x. p x ==> (x = infty) then infty
   else preal (inf (\r. 0 <= r /\ p (preal r)))`;

val _ = overload_on ("sup", Term `preal_sup`);
val _ = overload_on ("inf", Term `preal_inf`);

val le_sup_imp = store_thm
  ("le_sup_imp",
   ``!p x. p x ==> x <= sup p``,
   RW_TAC std_ss [preal_sup_def, le_infty]
   >> FULL_SIMP_TAC std_ss []
   >> Know `~p infty` >- METIS_TAC [infty_le]
   >> STRIP_TAC
   >> pcases_on `x`
   >> MATCH_MP_TAC preal_le
   >> RW_TAC real_ss []
   >> pcases_on `x'`
   >> MATCH_MP_TAC REAL_IMP_LE_SUP
   >> REVERSE CONJ_TAC >- (Q.EXISTS_TAC `y` >> RW_TAC real_ss [])
   >> Q.EXISTS_TAC `y'`
   >> RW_TAC std_ss []
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC le_preal
   >> METIS_TAC []);

val sup_le = store_thm
  ("sup_le",
   ``!p x. sup p <= x <=> (!y. p y ==> y <= x)``,
   RW_TAC std_ss [preal_sup_def, infty_le]
   >- (EQ_TAC >- RW_TAC std_ss [le_infty] >> METIS_TAC [])
   >> FULL_SIMP_TAC std_ss []
   >> Know `~p infty` >- METIS_TAC [infty_le]
   >> STRIP_TAC
   >> pcases_on `x` >- RW_TAC std_ss [le_infty]
   >> pcases_on `x'`
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >> pcases_on `y''`
       >> MATCH_MP_TAC le_trans
       >> Q.EXISTS_TAC `preal (sup (\r. (r = 0) \/ 0 <= r /\ p (preal r)))`
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC preal_le
       >> MATCH_MP_TAC REAL_IMP_LE_SUP
       >> REVERSE CONJ_TAC >- (Q.EXISTS_TAC `y'''` >> RW_TAC real_ss [])
       >> Q.EXISTS_TAC `y'`
       >> RW_TAC std_ss []
       >> RW_TAC std_ss []
       >> METIS_TAC [le_preal],
       RW_TAC std_ss []
       >> MATCH_MP_TAC preal_le
       >> MATCH_MP_TAC REAL_IMP_SUP_LE
       >> CONJ_TAC >- METIS_TAC []
       >> RW_TAC std_ss []
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC le_preal
       >> RW_TAC std_ss []]);

val le_sup = store_thm
  ("le_sup",
   ``!p x. x <= sup p <=> !y. (!z. p z ==> z <= y) ==> x <= y``,
   RW_TAC std_ss [preal_sup_def, le_infty]
   >> FULL_SIMP_TAC std_ss []
   >> pcases_on `x'`
   >> Q.PAT_X_ASSUM `~X` (K ALL_TAC)
   >> pcases_on `x`
   >- (RW_TAC std_ss [infty_le, preal_not_infty]
       >> Q.EXISTS_TAC `preal y`
       >> RW_TAC std_ss [preal_not_infty])
   >> ASM_SIMP_TAC real_ss [preal_le_eq]
   >> MATCH_MP_TAC (PROVE [] ``x /\ (y = z) ==> ((if x then y else w) = z)``)
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> MATCH_MP_TAC REAL_IMP_LE_SUP
       >> METIS_TAC [REAL_LE_REFL, le_preal])
   >> MP_TAC
      (Q.SPECL [`\r. (r = 0) \/ 0 <= r /\ p (preal r)`, `y'`] REAL_LE_SUP)
   >> MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
   >> CONJ_TAC >- METIS_TAC [le_preal]
   >> DISCH_THEN (fn th => REWRITE_TAC [th])
   >> RW_TAC std_ss []
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >> pcases_on `y''` >- RW_TAC std_ss [le_infty]
       >> MATCH_MP_TAC preal_le
       >> Q.PAT_X_ASSUM (`!a. (!b. P a b) ==> Q a`) MATCH_MP_TAC
       >> METIS_TAC [le_preal, preal_le],
       RW_TAC std_ss []
       >> MATCH_MP_TAC le_preal
       >> RW_TAC std_ss []
       >> FIRST_ASSUM MATCH_MP_TAC
       >> RW_TAC std_ss []
       >> pcases_on `z` >- METIS_TAC [infty_le, preal_not_infty]
       >> MATCH_MP_TAC preal_le
       >> METIS_TAC [le_preal, preal_le]]);

val sup_eq = store_thm
  ("sup_eq",
   ``!p x.
       (sup p = x) <=>
       (!y. p y ==> y <= x) /\ !y. (!z. p z ==> z <= y) ==> x <= y``,
   RW_TAC std_ss [le_antisym_eq, le_sup, sup_le]);

val sup_const = store_thm
  ("sup_const",
   ``!x. sup (\y. y = x) = x``,
   RW_TAC real_ss [sup_eq, le_refl]);

val sup_num = store_thm
  ("sup_num",
   ``sup (\x. ?n : num. x = & n) = infty``,
   MATCH_MP_TAC le_antisym
   >> RW_TAC std_ss [le_infty, le_sup]
   >> pcases_on `y` >- RW_TAC std_ss [le_refl]
   >> RW_TAC std_ss [infty_le, preal_not_infty]
   >> MP_TAC (Q.SPEC `y'` REAL_BIGNUM)
   >> PURE_REWRITE_TAC [real_lt]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `&n`)
   >> RW_TAC std_ss [posreal_of_num_def] >- METIS_TAC []
   >> METIS_TAC [le_preal]);

val sup_rmult = store_thm
  ("sup_rmult",
   ``!p f x.
       sup (\y. ?z : 'a. p z /\ (y = f z * x)) =
       sup (\y. ?z. p z /\ (y = f z)) * x``,
   REPEAT GEN_TAC
   >> Cases_on `x = 0`
   >- RW_TAC real_ss [mul_rzero, GSYM le_zero, sup_le, le_refl]
   >> MATCH_MP_TAC le_antisym
   >> RW_TAC real_ss [sup_le, le_sup]
   >- (MATCH_MP_TAC le_rmul_imp >> RW_TAC std_ss [le_sup] >> METIS_TAC [])
   >> REVERSE (Cases_on `?x. p x`)
   >- (Suff `sup (\y. ?z. p z /\ (y = f z)) = 0`
       >- RW_TAC real_ss [mul_lzero, zero_le]
       >> RW_TAC std_ss [GSYM le_zero, sup_le]
       >> METIS_TAC [])
   >> Cases_on `x = infty`
   >- (Cases_on `!z. p z ==> (f z = 0)`
       >- (Suff `sup (\y. ?z. p z /\ (y = f z)) = 0`
           >- RW_TAC real_ss [mul_lzero, zero_le]
           >> RW_TAC std_ss [GSYM le_zero, sup_le]
           >> METIS_TAC [le_zero])
       >> FULL_SIMP_TAC std_ss []
       >> Suff `infty <= y` >- RW_TAC real_ss [infty_le, le_infty]
       >> Q.PAT_X_ASSUM `!z. P z` MATCH_MP_TAC
       >> METIS_TAC [mul_rinfty])
   >> Suff `sup (\y. ?z. p z /\ (y = f z)) * x <= (y * inv x) * x`
   >- RW_TAC real_ss [mul_assoc, mul_linv, mul_rone]
   >> MATCH_MP_TAC le_rmul_imp
   >> RW_TAC real_ss [sup_le]
   >> Suff `(f z * x) * inv x <= y * inv x`
   >- RW_TAC real_ss [mul_assoc, mul_rinv, mul_rone]
   >> METIS_TAC [le_rmul_imp]);

val sup_lmult = store_thm
  ("sup_lmult",
   ``!p f x.
       sup (\y. ?z : 'a. p z /\ (y = x * f z)) =
       x * sup (\y. ?z. p z /\ (y = f z))``,
   ONCE_REWRITE_TAC [mul_comm]
   >> RW_TAC std_ss [sup_rmult]);

val sup_rmul = store_thm
  ("sup_rmul",
   ``!f x. sup (\y. ?z : 'a. y = f z * x) = sup (\y. ?z. y = f z) * x``,
   REPEAT GEN_TAC
   >> Suff
      `sup (\y. ?z : 'a. T /\ (y = f z * x)) = sup (\y. ?z. T /\ (y = f z)) * x`
   >- RW_TAC std_ss []
   >> SIMP_TAC pureSimps.pure_ss [sup_rmult]
   >> RW_TAC std_ss []);

val sup_lmul = store_thm
  ("sup_lmul",
   ``!f x. sup (\y. ?z : 'a. y = x * f z) = x * sup (\y. ?z. y = f z)``,
   ONCE_REWRITE_TAC [mul_comm]
   >> RW_TAC std_ss [sup_rmul]);

val sup_num_mul = store_thm
  ("sup_num_mul",
   ``!x. sup (\y. ?n : num. y = & n * x) = infty * x``,
   RW_TAC std_ss [sup_rmul, sup_num]);

val add_sup = store_thm
  ("add_sup",
   ``!p q.
       sup p + sup q =
       sup (\r. ?x y. (p x \/ (x = 0)) /\ (q y \/ (y = 0)) /\ (r = x + y))``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC EQ_SYM
   >> REWRITE_TAC [sup_eq]
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> MATCH_MP_TAC le_add2
       >> RW_TAC std_ss [le_sup_imp, zero_le])
   >> RW_TAC std_ss []
   >> Cases_on `y = infty` >- RW_TAC std_ss [le_infty]
   >> Cases_on `sup p = 0` >- RW_TAC std_ss [sup_le, add_lzero]
   >> Cases_on `sup q = 0` >- RW_TAC std_ss [sup_le, add_rzero]
   >> MATCH_MP_TAC le_trans
   >> Q.EXISTS_TAC `sup (\r. ?y. (q y \/ (y = 0)) /\ (r = sup p + y))`
   >> REVERSE CONJ_TAC
   >- (REVERSE (RW_TAC std_ss [sup_le]) >- RW_TAC std_ss [sup_le, add_rzero]
       >> Suff `sup p <= y - y'` >- RW_TAC std_ss [le_sub_eq]
       >> RW_TAC std_ss [sup_le]
       >> MATCH_MP_TAC le_sub_imp
       >> RW_TAC std_ss []
       >> METIS_TAC [])
   >> Cases_on `sup p = infty`
   >- (RW_TAC std_ss [add_linfty]
       >> Know `!r. (?y'. (q y' \/ (y' = 0)) /\ (r = infty)) = (r = infty)`
       >- METIS_TAC []
       >> RW_TAC std_ss [sup_const, le_refl])
   >> ONCE_REWRITE_TAC [add_comm]
   >> Suff `sup q <= sup (\r. ?y. (q y \/ (y = 0)) /\ (r = y + sup p)) - sup p`
   >- RW_TAC std_ss [le_sub_eq]
   >> RW_TAC std_ss [sup_le]
   >> MATCH_MP_TAC le_sub_imp
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [le_sup]
   >> METIS_TAC []);

val sup_le_sup_imp = store_thm
  ("sup_le_sup_imp",
   ``!p q. (!x. p x ==> ?y. q y /\ x <= y) ==> sup p <= sup q``,
   RW_TAC std_ss [sup_le] >> METIS_TAC [le_trans, le_sup_imp]);

val inf_le_imp = store_thm
  ("inf_le_imp",
   ``!p x. p x ==> inf p <= x``,
   RW_TAC std_ss [preal_inf_def, le_infty]
   >> FULL_SIMP_TAC std_ss []
   >> pcases_on `x` >- RW_TAC std_ss [le_infty]
   >> MATCH_MP_TAC preal_le
   >> MATCH_MP_TAC REAL_IMP_INF_LE
   >> CONJ_TAC >- METIS_TAC []
   >> METIS_TAC [REAL_LE_REFL]);

val le_inf = store_thm
  ("le_inf",
   ``!p x. x <= inf p <=> (!y. p y ==> x <= y)``,
   RW_TAC std_ss [preal_inf_def, le_infty]
   >> FULL_SIMP_TAC std_ss []
   >> pcases_on `x'`
   >> pcases_on `x`
   >- (RW_TAC std_ss [infty_le]
       >> MATCH_MP_TAC (PROVE [] ``~x /\ ~y ==> (x = y)``)
       >> REVERSE CONJ_TAC >- METIS_TAC []
       >> METIS_TAC [preal_not_infty])
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >> pcases_on `y''` >- RW_TAC std_ss [le_infty]
       >> MATCH_MP_TAC le_trans
       >> Q.EXISTS_TAC `preal (inf (\r. 0 <= r /\ p (preal r)))`
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC preal_le
       >> MATCH_MP_TAC REAL_IMP_INF_LE
       >> CONJ_TAC >- METIS_TAC []
       >> METIS_TAC [REAL_LE_REFL],
       RW_TAC std_ss []
       >> MATCH_MP_TAC preal_le
       >> MATCH_MP_TAC REAL_IMP_LE_INF
       >> CONJ_TAC >- METIS_TAC []
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC le_preal
       >> RW_TAC std_ss []]);

val inf_le = store_thm
  ("inf_le",
   ``!p x. inf p <= x <=> !y. (!z. p z ==> y <= z) ==> y <= x``,
   RW_TAC std_ss [preal_inf_def, le_infty] >- METIS_TAC [infty_le, le_infty]
   >> FULL_SIMP_TAC std_ss []
   >> pcases_on `x'`
   >> Q.PAT_X_ASSUM `~X` (K ALL_TAC)
   >> pcases_on `x` >- RW_TAC std_ss [infty_le, preal_not_infty, le_infty]
   >> RW_TAC real_ss [preal_le_eq]
   >> MP_TAC
      (Q.SPECL [`\r. 0 <= r /\ p (preal r)`, `y'`] REAL_INF_LE)
   >> MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
   >> CONJ_TAC >- METIS_TAC [le_preal]
   >> DISCH_THEN (fn th => REWRITE_TAC [th])
   >> RW_TAC std_ss []
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >> pcases_on `y''` >- METIS_TAC [infty_le, preal_not_infty]
       >> MATCH_MP_TAC preal_le
       >> Q.PAT_X_ASSUM (`!a. (!b. P a b) ==> Q a`) MATCH_MP_TAC
       >> METIS_TAC [le_preal, preal_le],
       RW_TAC std_ss []
       >> MATCH_MP_TAC le_preal
       >> RW_TAC std_ss []
       >> FIRST_ASSUM MATCH_MP_TAC
       >> RW_TAC std_ss []
       >> pcases_on `z` >- RW_TAC std_ss [le_infty]
       >> MATCH_MP_TAC preal_le
       >> METIS_TAC [le_preal, preal_le]]);

(* ------------------------------------------------------------------------- *)
(* (posreal,<=) is a complete lattice                                        *)
(* ------------------------------------------------------------------------- *)

val posreal_def = Define `posreal = \x : posreal. T`;

val sup_lub = store_thm
  ("sup_lub",
   ``!p. lub (posreal, (<=)) p (sup p)``,
   RW_TAC std_ss [lub_def, posreal_def, le_sup_imp, sup_le]);

val inf_glb = store_thm
  ("inf_glb",
   ``!p. glb (posreal, (<=)) p (inf p)``,
   RW_TAC std_ss [glb_def, posreal_def, le_inf, inf_le_imp]);

val posreal_complete = store_thm
  ("posreal_complete",
   ``complete (posreal, (<=))``,
   RW_TAC std_ss [complete_def]
   >> METIS_TAC [sup_lub, inf_glb]);

(* ------------------------------------------------------------------------- *)
(* A calculator for rational posreals.                                       *)
(* ------------------------------------------------------------------------- *)

val add_rat = store_thm
  ("add_rat",
   ``!a b c d : num.
       & a / & b + & c / & d =
       if a = 0 then & c / & d
       else if b = 0 then infty
       else if c = 0 then & a / & b
       else if d = 0 then infty
       else & (a * d + b * c) / & (b * d)``,
   RW_TAC std_ss [div_lzero, add_lzero, div_rzero, posreal_of_num_inj,
                  add_linfty, add_rzero, add_rinfty]
   >> RW_TAC std_ss [preal_div, posreal_of_num_def, REAL_POS, REAL_INJ,
                     MULT_EQ_0, ADD_EQ_0, REAL_LE_DIV, preal_add,
                     REAL_ADD_RAT, REAL_MUL, REAL_ADD]);

val add_ratl = store_thm
  ("add_ratl",
   ``!c a b : num.
       & a / & b + & c =
       if c = 0 then & a / & b
       else if a = 0 then & c
       else if b = 0 then infty
       else & (a + b * c) / & b``,
   REPEAT GEN_TAC
   >> MP_TAC (Q.SPEC `& c` div_rone)
   >> DISCH_THEN (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   >> RW_TAC std_ss
      [add_rat, div_rone, mul_rone, div_lzero, div_rzero, posreal_of_num_inj,
       MULT_RIGHT_1]);

val add_ratr = store_thm
  ("add_ratr",
   ``!c a b : num.
       & c + & a / & b =
       if c = 0 then & a / & b
       else if a = 0 then & c
       else if b = 0 then infty
       else & (c * b + a) / & b``,
   METIS_TAC [add_lzero, preal_div_def, mul_lzero, add_rzero, div_rzero, add_rinfty, add_ratl, ADD_COMM, add_comm, MULT_COMM]);

val sub_rat = store_thm
  ("sub_rat",
   ``!a b c d : num.
       & a / & b - & c / & d =
       if a = 0 then 0
       else if b = 0 then
         if d = 0 then unint (-) (& a / & b) (& c / & d) else infty
       else if c = 0 then & a / & b
       else if d = 0 then 0
       else & (a * d - b * c) / & (b * d)``,
   RW_TAC std_ss [div_lzero, sub_lzero, div_rzero, posreal_of_num_inj,
                  sub_rzero, unint_def]
   >> RW_TAC std_ss [preal_div, posreal_of_num_def, REAL_POS, REAL_INJ,
                     sub_linfty, preal_not_infty, sub_rinfty,
                     MULT_EQ_0, ADD_EQ_0, REAL_LE_DIV, preal_sub,
                     REAL_SUB, REAL_SUB_RAT, REAL_MUL]
   >> RW_TAC std_ss
      [preal_eq_zero, GSYM posreal_of_num_def, GSYM REAL_NEG_GE0,
       real_div, REAL_MUL_LNEG, REAL_NEGNEG]
   >> MATCH_MP_TAC REAL_LE_MUL
   >> RW_TAC std_ss [REAL_POS, REAL_LE_INV]);

val sub_ratl = store_thm
  ("sub_ratl",
   ``!c a b : num.
       & a / & b - & c =
       if c = 0 then & a / & b
       else if a = 0 then 0
       else if b = 0 then infty
       else & (a - b * c) / & b``,
   REPEAT GEN_TAC
   >> MP_TAC (Q.SPEC `& c` div_rone)
   >> DISCH_THEN (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   >> ONCE_REWRITE_TAC [sub_rat]
   >> RW_TAC std_ss
      [div_rone, mul_rone, div_lzero, div_rzero, posreal_of_num_inj,
       MULT_RIGHT_1, sub_rzero, sub_lzero, sub_linfty,
       posreal_of_num_not_infty, preal_sub, preal_div, REAL_POS]);

val sub_ratr = store_thm
  ("sub_ratr",
   ``!c a b : num.
       & c - & a / & b =
       if c = 0 then 0
       else if a = 0 then & c
       else if b = 0 then 0
       else & (b * c - a) / & b``,
   REPEAT GEN_TAC
   >> MP_TAC (Q.SPEC `& c` div_rone)
   >> DISCH_THEN (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   >> ONCE_REWRITE_TAC [sub_rat]
   >> RW_TAC std_ss
      [div_rone, mul_rone, div_lzero, div_rzero, posreal_of_num_inj,
       MULT_RIGHT_1, sub_rzero, sub_lzero, sub_linfty,
       posreal_of_num_not_infty, preal_sub, preal_div, REAL_POS,
       MULT_LEFT_1]
   >> METIS_TAC [MULT_COMM]);

val sub_linfty_rat = store_thm
  ("sub_linfty_rat",
   ``!a b.
       infty - & a / & b =
       if b = 0 then unint (-) infty (& a / & b) else infty``,
   RW_TAC std_ss
   [preal_div, REAL_POS, posreal_of_num_def, REAL_INJ, sub_linfty,
    preal_not_infty, unint_def]);

val sub_linfty_num = store_thm
  ("sub_linfty_num",
   ``!a b. infty - & a = infty``,
   RW_TAC std_ss [posreal_of_num_def, sub_linfty, preal_not_infty]);

val sub_rinfty_rat = store_thm
  ("sub_rinfty_rat",
   ``!a b.
       & a / & b - infty = if b = 0 then unint (-) (& a / & b) infty else 0``,
   RW_TAC std_ss
   [preal_div, REAL_POS, posreal_of_num_def, REAL_INJ, sub_rinfty,
    preal_not_infty, unint_def]);

val sub_rinfty_num = store_thm
  ("sub_rinfty_num",
   ``!a b. & a - infty = 0``,
   RW_TAC std_ss [posreal_of_num_def, sub_rinfty, preal_not_infty]);

val mul_rat = store_thm
  ("mul_rat",
   ``!a b c d : num. (& a / & b) * (& c / & d) = & (a * c) / & (b * d)``,
   RW_TAC std_ss
   [preal_div_def, inv_mul, entire, posreal_of_num_inj, GSYM posreal_of_num_mul]
   >> Cases_on `a = 0`
   >> Cases_on `c = 0`
   >> RW_TAC std_ss
      [mul_lzero, mul_rzero, mul_linfty, mul_rinfty, inv_zero,
       posreal_of_num_inj, inv_eq_zero, entire, posreal_of_num_not_infty]
   >> FULL_SIMP_TAC std_ss []
   >> METIS_TAC [mul_comm, mul_assoc]);

val mul_ratl = store_thm
  ("mul_ratl",
   ``!c a b : num. (& a / & b) * & c = & (a * c) / & b``,
   METIS_TAC [mul_rat, div_rone, MULT_RIGHT_1]);

val mul_ratr = store_thm
  ("mul_ratr",
   ``!c a b : num. &c * (& a / & b) = & (c * a) / & b``,
   METIS_TAC [mul_rat, div_rone, MULT_LEFT_1]);

val mul_linfty_rat = store_thm
  ("mul_linfty_rat",
   ``!a b : num. infty * (& a / & b) = if a = 0 then 0 else infty``,
   RW_TAC std_ss
   [mul_linfty, div_eq_zero, posreal_of_num_inj, posreal_of_num_not_infty]);

val mul_linfty_num = store_thm
  ("mul_linfty_num",
   ``!a : num. infty * & a = if a = 0 then 0 else infty``,
   RW_TAC std_ss [mul_linfty, posreal_of_num_inj, posreal_of_num_not_infty]);

val mul_rinfty_rat = store_thm
  ("mul_rinfty_rat",
   ``!a b : num. (& a / & b) * infty = if a = 0 then 0 else infty``,
   RW_TAC std_ss
   [mul_rinfty, div_eq_zero, posreal_of_num_inj, posreal_of_num_not_infty]);

val mul_rinfty_num = store_thm
  ("mul_rinfty_num",
   ``!a : num. & a * infty = if a = 0 then 0 else infty``,
   RW_TAC std_ss [mul_rinfty, posreal_of_num_inj, posreal_of_num_not_infty]);

val mul_infty_infty = store_thm
  ("mul_infty_infty",
   ``infty * infty = infty``,
   RW_TAC std_ss [mul_linfty, posreal_of_num_not_infty]);

val div_rat = store_thm
  ("div_rat",
   ``!a b c d : num.
       (& a / & b) / (& c / & d) =
       if c = 0 then if a = 0 then 0 else infty
       else & (a * d) / & (b * c)``,
   REPEAT GEN_TAC
   >> Cases_on `a = 0`
   >> Cases_on `b = 0`
   >> Cases_on `c = 0`
   >> Cases_on `d = 0`
   >> RW_TAC std_ss
      [mul_lzero, mul_rzero, mul_linfty, mul_rinfty, inv_zero, inv_inv,
       posreal_of_num_inj, inv_eq_zero, entire, posreal_of_num_not_infty,
       preal_div_def, inv_mul, entire, GSYM posreal_of_num_mul, inv_eq_infty]
   >> METIS_TAC [mul_comm, mul_assoc]);

val div_ratl = store_thm
  ("div_ratl",
   ``!c a b : num.
       (& a / & b) / & c =
       if c = 0 then if a = 0 then 0 else infty
       else & a / & (b * c)``,
   METIS_TAC [div_rat, div_rone, MULT_RIGHT_1]);

val div_ratr = store_thm
  ("div_ratr",
   ``!c a b : num.
       & c / (& a / & b) =
       if a = 0 then if c = 0 then 0 else infty
       else & (c * b) / & a``,
   METIS_TAC [div_rat, div_rone, MULT_LEFT_1]);

val div_rzero_num = store_thm
  ("div_rzero_num",
   ``!n. & n / 0 = if n = 0 then 0 else infty``,
   RW_TAC std_ss [div_rzero, posreal_of_num_inj]);

val div_rzero_rat = store_thm
  ("div_rzero_rat",
   ``!a b. (& a / & b) / 0 = if a = 0 then 0 else infty``,
   RW_TAC std_ss [div_rzero, div_eq_zero, posreal_of_num_inj,
                  posreal_of_num_not_infty]);

val div_linfty_num = store_thm
  ("div_linfty_num",
   ``!a. infty / & a = infty``,
   RW_TAC std_ss [div_linfty, posreal_of_num_not_infty]);

val div_linfty_rat = store_thm
  ("div_linfty_rat",
   ``!a b. infty / (& a / & b) = if ~(a = 0) /\ (b = 0) then 0 else infty``,
   RW_TAC std_ss [div_linfty, div_eq_infty, posreal_of_num_not_infty,
                  posreal_of_num_inj]);

val le_rat = store_thm
  ("le_rat",
   ``!a b c d.
       & a / & b <= & c / & d <=>
       if d = 0 then (a = 0) \/ ~(c = 0) else a * d <= b * c``,
   REPEAT GEN_TAC
   >> Cases_on `a = 0`
   >> Cases_on `b = 0`
   >> Cases_on `c = 0`
   >> Cases_on `d = 0`
   >> RW_TAC arith_ss
      [div_rzero, le_refl, zero_le, div_lzero, posreal_of_num_inj, le_infty,
       infty_le, posreal_of_num_not_infty, div_eq_infty, le_zero, div_eq_zero]
   >> RW_TAC std_ss [le_eq_sub_zero]
   >> ONCE_REWRITE_TAC [sub_rat]
   >> RW_TAC arith_ss
      [div_eq_infty, posreal_of_num_inj, posreal_of_num_not_infty,
       div_eq_zero]);

val le_ratl = store_thm
  ("le_ratl",
   ``!c a b. & a / & b <= & c <=> a <= b * c``,
   METIS_TAC [le_rat, div_rone, MULT_RIGHT_1, ONE, SUC_NOT]);

val le_ratr = store_thm
  ("le_ratr",
   ``!c a b.
       & c <= & a / & b <=> if b = 0 then (c = 0) \/ ~(a = 0) else c * b <= a``,
   METIS_TAC [le_rat, div_rone, MULT_LEFT_1]);

val eq_rat = store_thm
  ("eq_rat",
   ``!a b c d.
       (& a / & b = & c / & d) <=>
       if a = 0 then c = 0 else ~(c = 0) /\ (a * d = b * c)``,
   RW_TAC arith_ss [le_antisym_eq, le_rat]
   >> Cases_on `c = 0` >- RW_TAC arith_ss []
   >> METIS_TAC [LESS_EQUAL_ANTISYM, LESS_EQ_REFL, MULT_COMM]);

val eq_ratl = store_thm
  ("eq_ratl",
   ``!a b c. (& a / & b = & c) <=> if a = 0 then c = 0 else a = b * c``,
   REPEAT GEN_TAC
   >> MP_TAC (Q.SPEC `& c` div_rone)
   >> DISCH_THEN (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   >> RW_TAC std_ss [eq_rat, mul_rone]
   >> Cases_on `c = 0`
   >> RW_TAC std_ss [mul_rzero, MULT_0, MULT_RIGHT_1]);

val rat_eq_infty = store_thm
  ("rat_eq_infty",
   ``!a b. (& a / & b = infty) <=> ~(a = 0) /\ (b = 0)``,
   RW_TAC std_ss [div_eq_infty, posreal_of_num_inj, posreal_of_num_not_infty]);

Theorem rat_cancel:
  !a b c. (& a * & b) / (& a * & c) = if a = 0 then 0 else & b / & c
Proof
   (RW_TAC std_ss [preal_div_def, mul_lzero, inv_mul, entire,
                  posreal_of_num_inj]
    >> FULL_SIMP_TAC std_ss [DE_MORGAN_THM, inv_zero])
   >- (Cases_on `& b = 0`
       >> RW_TAC std_ss [mul_assoc, mul_rinfty, mul_rzero, posreal_of_num_inj])
   >> MP_TAC (METIS_PROVE [mul_assoc, mul_comm]
              ``!a b c d : posreal. (a * b) * (c * d) = (a * c) * (b * d)``)
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> RW_TAC std_ss
      [mul_rinv, posreal_of_num_not_infty, posreal_of_num_inj, mul_lone]
QED

val min_num = store_thm
  ("min_num",
   ``!m n. min (& m) (& n) = if m <= n then & m else & n``,
   RW_TAC std_ss [preal_min_def, posreal_of_num_le]);

val min_ratl = store_thm
  ("min_ratl",
   ``!m a b.
       min (& a / & b) (& m) =
       if (a = 0) \/ a <= b * m then & a / & b else & m``,
   REPEAT STRIP_TAC
   >> Cases_on `a = 0` >- RW_TAC std_ss [div_lzero, min_lzero]
   >> RW_TAC std_ss [preal_min_def]
   >| [MATCH_MP_TAC le_antisym
       >> RW_TAC std_ss [le_ratr]
       >> PROVE_TAC [LESS_EQ_CASES, MULT_COMM, ZERO_LESS_EQ],
       Suff `F` >- PROVE_TAC []
       >> Q.PAT_X_ASSUM `~(X <= Y)` MP_TAC
       >> RW_TAC std_ss [le_ratl]]);

val min_ratr = store_thm
  ("min_ratr",
   ``!m a b.
       min (& m) (& a / & b) =
       if (a = 0) \/ a <= b * m then & a / & b else & m``,
   PROVE_TAC [min_ratl, min_comm]);

val min_rat = store_thm
  ("min_rat",
   ``!a b c d.
       min (& a / & b) (& c / & d) =
       if (a = 0) \/ (~(c = 0) /\ d * a <= c * b) then & a / & b
       else & c / & d``,
   REPEAT STRIP_TAC
   >> Cases_on `a = 0` >- RW_TAC std_ss [div_lzero, min_lzero]
   >> Cases_on `c = 0` >- RW_TAC std_ss [div_lzero, min_rzero]
   >> RW_TAC std_ss [preal_min_def, eq_rat, le_rat]
   >> FULL_SIMP_TAC arith_ss []
   >> PROVE_TAC [MULT_COMM, LESS_EQ_CASES, LESS_EQUAL_ANTISYM]);

val max_num = store_thm
  ("max_num",
   ``!m n. max (& m) (& n) = if m <= n then & n else & m``,
   RW_TAC std_ss [preal_max_def, posreal_of_num_le]);

val max_ratl = store_thm
  ("max_ratl",
   ``!m a b.
       max (& a / & b) (& m) =
       if (a = 0) \/ a <= b * m then & m else & a / & b``,
   REPEAT STRIP_TAC
   >> Cases_on `a = 0` >- RW_TAC std_ss [div_lzero, max_lzero]
   >> RW_TAC std_ss [preal_max_def]
   >| [MATCH_MP_TAC le_antisym
       >> RW_TAC std_ss [le_ratr]
       >> PROVE_TAC [LESS_EQ_CASES, MULT_COMM, ZERO_LESS_EQ],
       Suff `F` >- PROVE_TAC []
       >> Q.PAT_X_ASSUM `~(X <= Y)` MP_TAC
       >> RW_TAC std_ss [le_ratl]]);

val max_ratr = store_thm
  ("max_ratr",
   ``!m a b.
       max (& m) (& a / & b) =
       if (a = 0) \/ a <= b * m then & m else & a / & b``,
   PROVE_TAC [max_ratl, max_comm]);

val max_rat = store_thm
  ("max_rat",
   ``!a b c d.
       max (& a / & b) (& c / & d) =
       if (a = 0) \/ (~(c = 0) /\ d * a <= c * b) then & c / & d
       else & a / & b``,
   REPEAT STRIP_TAC
   >> Cases_on `a = 0` >- RW_TAC std_ss [div_lzero, max_lzero]
   >> Cases_on `c = 0` >- RW_TAC std_ss [div_lzero, max_rzero]
   >> RW_TAC std_ss [preal_max_def, eq_rat, le_rat]
   >> FULL_SIMP_TAC arith_ss []
   >> PROVE_TAC [MULT_COMM, LESS_EQ_CASES, LESS_EQUAL_ANTISYM]);

val bound1_num = store_thm
  ("bound1_num",
   ``!m. bound1 (& m) = if m = 0 then 0 else 1``,
   RW_TAC std_ss [bound1_min, min_num, posreal_of_num_inj]
   >> DECIDE_TAC);

val bound1_rat = store_thm
  ("bound1_rat",
   ``!a b. bound1 (& a / & b) = if a <= b then & a / & b else 1``,
   RW_TAC std_ss [bound1_min, min_ratl]
   >> FULL_SIMP_TAC arith_ss []);

val _ = export_theory();
