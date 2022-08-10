open HolKernel Parse boolLib;

open bossLib hurdUtils miller_rabinTheory state_transformerTheory
     pairTheory arithmeticTheory combinTheory prob_uniformTheory
     extra_numTheory probTheory;

val _ = new_theory "miller_rabin_ml";

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val REVERSE = Tactical.REVERSE;

infixr 0 oo ## ++ << || THENC ORELSEC THENR ORELSER -->;
infix 1 >> |->;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Some standard tools.                                                      *)
(* ------------------------------------------------------------------------- *)

val Strip = !! STRIP_TAC;
val Simplify = RW_TAC std_ss;

(* ========================================================================= *)
(* miller_rabin_ml theory.                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_ML = save_thm ("UNCURRY_ML", pairTheory.UNCURRY_DEF);

val EVEN_ML = store_thm
  ("EVEN_ML",
   ``!n. EVEN n = (n MOD 2 = 0)``,
   Strip
   ++ RW_TAC std_ss [MOD_TWO]
   ++ DECIDE_TAC);

val ODD_ML = store_thm
  ("ODD_ML",
   ``ODD = $~ o EVEN``,
   FUN_EQ_TAC
   ++ RW_TAC std_ss [o_DEF, EVEN_ODD]);

val UNIT_ML = store_thm
  ("UNIT_ML",
   ``!x. UNIT x = \s. (x, s)``,
   RW_TAC std_ss [UNIT_DEF]);

val BIND_ML = store_thm
  ("BIND_ML",
   ``!f g. BIND f g = UNCURRY g o f``,
   RW_TAC std_ss [BIND_DEF]);

val MANY_ML = store_thm
  ("MANY_ML",
   ``!f n.
       many f n =
       if n = 0 then UNIT T
       else BIND f (\x. if x then many f (n - 1) else UNIT F)``,
   STRIP_TAC
   ++ Cases
   ++ RW_TAC std_ss [MANY, SUC_SUB1]);

val LOG2_ML = store_thm
  ("LOG2_ML",
   ``!n. log2 n = if n = 0 then 0 else SUC (log2 (n DIV 2))``,
   Cases
   ++ RW_TAC std_ss [log2_def, SUC_SUB1]);

val PROB_UNIF_ML = store_thm
  ("PROB_UNIF_ML",
   ``!n s.
        prob_unif n s =
        if n = 0 then (0, s)
        else
          let (m, s') = prob_unif (n DIV 2) s
          in (if shd s' then 2 * m + 1 else 2 * m, stl s')``,
   Cases
   ++ RW_TAC std_ss [prob_unif_def, SUC_SUB1]);

val PROB_UNIFORM_CUT_ML = store_thm
  ("PROB_UNIFORM_CUT_ML",
   ``!t n.
       prob_uniform_cut t n =
       if n = 0 then prob_uniform_cut t n
       else if t = 0 then UNIT 0
       else
         BIND (prob_unif (n - 1))
         (\m. if m < n then UNIT m else prob_uniform_cut (t - 1) n)``,
   Cases
   ++ Cases
   ++ RW_TAC std_ss [PROB_UNIFORM_CUT_MONAD, SUC_SUB1]);

val FACTOR_TWOS_ML = save_thm ("FACTOR_TWOS_ML", factor_twos_def);

val MODEXP_ML = save_thm ("MODEXP_ML", modexp_def);

val WITNESS_TAIL_ML = store_thm
  ("WITNESS_TAIL_ML",
   ``!n a r.
       witness_tail n a r =
       if r = 0 then ~(a = 1)
       else
         let a2 = (a * a) MOD n
         in if a2 = 1 then ~(a = 1) /\ ~(a = n - 1)
            else witness_tail n a2 (r - 1)``,
   Cases_on `r`
   ++ RW_TAC std_ss [witness_tail_def, SUC_SUB1]);

val WITNESS_ML = save_thm ("WITNESS_ML", witness_def);

val MILLER_RABIN_1_ML = save_thm ("MILLER_RABIN_1_ML", miller_rabin_1_def);

val MILLER_RABIN_ML = save_thm ("MILLER_RABIN_ML", miller_rabin_def);

(* non-interactive mode
*)
val _ = export_theory ();
