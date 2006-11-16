(* ========================================================================= *)
(* Example verifications of probabilistic programs.                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* ------------------------------------------------------------------------- *)
loadPath := ["../src"] @ !loadPath;
app load
  ["bossLib","realLib","rich_listTheory","intLib","stringTheory","metisLib",
   "posrealLib","wpTheory","valueTheory","looprulesTheory","pgclLib"];
quietdec := true;

open HolKernel Parse boolLib bossLib intLib realLib metisLib;
open combinTheory listTheory rich_listTheory stringTheory
     arithmeticTheory integerTheory realTheory pgclLib;
open posetTheory posrealTheory posrealLib expectationTheory wpTheory pgclLib;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;

quietdec := false;

(* ------------------------------------------------------------------------- *)
(* Prob choice then demon choice  versus  demon choice then prob choice.     *)
(* ------------------------------------------------------------------------- *)

val prob_then_demon = Count.apply prove
  (``wp (Seq (ProbAssign "i" [0; 1]) (NondetAssign "j" [0; 1]))
     (\v : int state. if v"i" = v"j" then 1 else 0) = \v. 0``,
   RW_TAC arith_ss
   [wp_def, ProbAssign_def, Probs_def, NondetAssign_def, assign_eta, lin_eta,
    Nondets_def, MAP, LENGTH, CHR_11, FUN_EQ_THM, Zero_def, Min_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ FULL_SIMP_TAC int_ss []
   ++ FULL_SIMP_TAC posreal_reduce_ss [bound1_def]);

val demon_then_prob = Count.apply prove
  (``wp (Seq (NondetAssign "j" [0; 1]) (ProbAssign "i" [0; 1]))
     (\v : int state. if v"i" = v"j" then 1 else 0) = \v. 1 / 2``,
   RW_TAC arith_ss
   [wp_def, ProbAssign_def, Probs_def, NondetAssign_def, assign_eta, lin_eta,
    Nondets_def, MAP, LENGTH, CHR_11, FUN_EQ_THM, Zero_def, Min_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ FULL_SIMP_TAC int_ss []
   ++ FULL_SIMP_TAC posreal_reduce_ss [bound1_def]);

val partial_demon_then_prob = Count.apply prove
  (``Leq (\v : int state. 1 / 2)
     (wlp (Seq (NondetAssign "j" [0; 1]) (ProbAssign "i" [0; 1]))
      (\v. if v"i" = v"j" then 1 else 0))``,
   RW_TAC arith_ss
   [ProbAssign_def, Probs_def, NondetAssign_def,
    Nondets_def, MAP, LENGTH, CHR_11, Program_def]
   ++ RW_TAC posreal_reduce_ss []
   ++ pure_wlp_tac
   ++ leq_tac);

(* ------------------------------------------------------------------------- *)
(* Infinite loops.                                                           *)
(* ------------------------------------------------------------------------- *)

val wp_loop = Count.apply prove
  (``!post. wp (While (\s. T) Skip) post = Zero``,
   RW_TAC std_ss [wp_def, cond_eta, wp_skip]
   ++ Know `monotonic (expect,Leq) (\e s : 'a state. e s)`
   >> (RW_TAC std_ss [monotonic_def]
       ++ CONV_TAC (DEPTH_CONV ETA_CONV)
       ++ RW_TAC std_ss [])
   ++ RW_TAC std_ss []
   ++ Know `lfp (expect,Leq) (\e s : 'a state. e s) (expect_lfp (\e s. e s))`
   >> METIS_TAC [expect_lfp_def]
   ++ RW_TAC std_ss []
   ++ Suff `lfp (expect,Leq) (\e s : 'a state. e s) Zero`
   >> METIS_TAC [lfp_def, expect_def, leq_antisym, leq_refl]
   ++ RW_TAC std_ss [lfp_def, expect_def, zero_leq]
   ++ CONV_TAC (DEPTH_CONV ETA_CONV)
   ++ RW_TAC std_ss []);

val wlp_loop = Count.apply prove
  (``!post. wlp (While (\s. T) Skip) post = Magic``,
   RW_TAC std_ss [wlp_def, cond_eta, wlp_skip]
   ++ Know `monotonic (expect,Leq) (\e s : 'a state. e s)`
   >> (RW_TAC std_ss [monotonic_def]
       ++ CONV_TAC (DEPTH_CONV ETA_CONV)
       ++ RW_TAC std_ss [])
   ++ RW_TAC std_ss []
   ++ Know `gfp (expect,Leq) (\e s : 'a state. e s) (expect_gfp (\e s. e s))`
   >> METIS_TAC [expect_gfp_def]
   ++ RW_TAC std_ss []
   ++ Suff `gfp (expect,Leq) (\e s : 'a state. e s) Magic`
   >> METIS_TAC [gfp_def, expect_def, leq_antisym, leq_refl]
   ++ RW_TAC std_ss [gfp_def, expect_def, leq_magic]
   ++ CONV_TAC (DEPTH_CONV ETA_CONV)
   ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Monty Hall                                                                *)
(* ------------------------------------------------------------------------- *)

val monty_hide_def = Define
  `monty_hide : int command = NondetAssign "pc" [1; 2; 3]`;

val monty_choose_def = Define
  `monty_choose : int command = ProbAssign "cc" [1; 2; 3]`;

val monty_reveal_def = Define
  `monty_reveal : int command =
   Guards [((\v. ~(v"pc" = 1) /\ ~(v"cc" = 1)), (Assign "ac" (\v. 1)));
           ((\v. ~(v"pc" = 2) /\ ~(v"cc" = 2)), (Assign "ac" (\v. 2)));
           ((\v. ~(v"pc" = 3) /\ ~(v"cc" = 3)), (Assign "ac" (\v. 3)))]`;

val monty_switch_def = Define
  `monty_switch switch : int command =
   if ~switch then Skip
   else Assign "cc" (\v. if ~(v"cc" = 1) /\ ~(v"ac" = 1) then 1
                         else if ~(v"cc" = 2) /\ ~(v"ac" = 2) then 2 else 3)`;

val monty_hall_def = Define
  `monty_hall switch =
   Program [monty_hide;
            monty_choose;
            monty_reveal;
            monty_switch switch]`;

(* Partial correctness using the wlp verification condition generator *)

val partial_monty_hall = Count.apply prove
  (``!switch.
       Leq (\v. if switch then 2 / 3 else 1 / 3)
       (wlp (monty_hall switch) (\v. if v"pc" = v"cc" then 1 else 0))``,
   RW_TAC std_ss
     [monty_hall_def, monty_switch_def, monty_reveal_def,
      monty_choose_def, monty_hide_def]
   ++ wlp_tac);

(* Total correctness by hand *)

val monty_hall = Count.apply prove
  (``!switch.
       wp (monty_hall switch) (\v. if v"pc" = v"cc" then 1 else 0) =
       (\v. if switch then 2 / 3 else 1 / 3)``,
   CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC std_ss [wp_def, monty_hall_def, seq_assoc, Program_def]
   ++ RW_TAC std_ss [monty_switch_def, wp_def, wp_skip, CHR_11, assign_def]
   ++ RW_TAC int_ss [wp_def, Guards_def, guards_def, wp_if, Nondets_def,
                     monty_reveal_def, Min_def, cond_eta, assign_def]
   ++ RW_TAC posreal_ss [CHR_11]
   ++ RW_TAC list_ss [monty_choose_def, wp_def, ProbAssign_def, Probs_def,
                      CHR_11, assign_def, lin_eta]
   ++ RW_TAC int_ss []
   ++ RW_TAC posreal_reduce_ss []
   ++ RW_TAC posreal_ss [Zero_def]
   ++ RW_TAC int_ss [monty_hide_def, MAP, wp_def, NondetAssign_def,
                     Nondets_def, Min_def, assign_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC posreal_reduce_ss []);
  
(* ------------------------------------------------------------------------- *)
(* The random walker                                                         *)
(* ------------------------------------------------------------------------- *)

val lurch_def = Define
  `lurch : int command =
   Prob (\v. 1/2) (Assign "n" (\v. v"n" - 1)) (Assign "n" (\v. v"n" + 1))`;

val walk_def = Define `walk = While (\v. v"n" = 0) lurch`;

val lurch_once = Count.apply prove
  (``!r.
       wp lurch r =
       (\v.
          (1 / 2) * r (\w. if w = "n" then v"n" - 1 else v w) +
          (1 / 2) * r (\w. if w = "n" then v"n" + 1 else v w))``,
   RW_TAC posreal_ss
     [wp_def, lurch_def, bound1_basic, COND_RAND, assign_eta, lin_eta,
      FUN_EQ_THM]
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC posreal_reduce_ss []);

val lurch_once_home = Count.apply prove
  (``wp lurch (\v. if v"n" = 0 then 1 else 0) =
     (\v. if ABS (v"n") = 1 then 1 / 2 else 0)``,
   RW_TAC real_ss [lurch_once]
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC posreal_ss [INT_ABS_EQ]
   ++ Suff `F` >> REWRITE_TAC []
   ++ COOPER_TAC);

val lurch_once_home' = Count.apply prove
  (``Leq (\v. if ABS (v"n") = 1 then 1 / 2 else 0)
     (wlp lurch (\v. if v"n" = 0 then 1 else 0))``,
   RW_TAC real_ss [lurch_def]
   ++ wlp_tac
   ++ COOPER_TAC);

(*
val walk_terminates = Count.apply prove
  (``!s. wp walk One = One``,
*)

(* ------------------------------------------------------------------------- *)
(* Rabin's probabilistic mutual exclusion algorithm                          *)
(* ------------------------------------------------------------------------- *)

val rabin_invar1_def = Define
  `rabin_invar1 i n : posreal =
   1 - (if i = n then & (Num n + 1) / & (2 ** (Num n))
        else if i = n + 1 then 1 / & (2 ** (Num n)) else 0)`;

val rabin_invar2_def = Define
  `rabin_invar2 i n : posreal =
   if i = n then & (Num n) / & (2 ** (Num n))
   else if i = n + 1 then 1 / & (2 ** (Num n)) else 0`;

val rabin_def = Define
  `rabin : int command =
   While (\v. 1 < v"i")
   (Program [Assign "n" (\v. v"i");
             While (\v. 0 < v"n")
             (Program [ProbAssign "d" [0; 1];
                       Assign "i" (\v. v"i" - v"d");
                       Assign "n" (\v. v"n" - 1)])])`;

val annotated_rabin_def = Define
  `annotated_rabin : int command =
   Assert (\v. if v"i" = 1 then 1 else if 1 < v"i" then 2 / 3 else 0)
   (While (\v. 1 < v"i")
    (Program [Assign "n" (\v. v"i");
              Assert (\v. if 0 <= v"n" /\ v"n" <= v"i" then
                            (2 / 3) * rabin_invar1 (v"i") (v"n")
                            + rabin_invar2 (v"i") (v"n")
                          else 0)
              (While (\v. 0 < v"n")
               (Program [ProbAssign "d" [0; 1];
                         Assign "i" (\v. v"i" - v"d");
                         Assign "n" (\v. v"n" - 1)]))]))`;

val annotated_rabin = Count.apply prove
  (``annotated_rabin = rabin``,
   RW_TAC std_ss [annotated_rabin_def, Assert_def, rabin_def]);

val partial_rabin = Count.apply prove
  (``Leq (\v. if v"i" = 1 then 1 else if 1 < v"i" then 2 / 3 else 0)
     (wlp rabin (\v. if v"i" = 1 then 1 else 0))``,
   (RW_TAC std_ss [annotated_rabin_def, GSYM annotated_rabin]
    ++ wlp_tac
    ++ TRY (Suff `F` >> METIS_TAC [] ++ COOPER_TAC)
    ++ ASM_SIMP_TAC posreal_ss [rabin_invar1_def, rabin_invar2_def]
    ++ REPEAT (if_cases_tac wlp_assume_tac)
    ++ TRY (Suff `F` >> METIS_TAC [] ++ COOPER_TAC)
    ++ IMP_RES_TAC LE_NUM_OF_INT
    ++ Q.PAT_ASSUM `0i <= X`
       (fn th => MP_TAC (REWRITE_RULE [GSYM INT_OF_NUM] th) ++ ASSUME_TAC th)
    ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
    ++ RW_TAC std_ss [NUM_OF_INT, INT_SUB]
    ++ Q.PAT_ASSUM `X <= Num Y` MP_TAC)
   << [POP_ASSUM_LIST (K ALL_TAC)
       ++ Q.SPEC_TAC (`Num (s "n")`, `k`)
       ++ Cases
       ++ RW_TAC arith_ss [EXP]
       ++ Know `~(2n ** n = 0)` >> RW_TAC arith_ss [EXP_EQ_0]
       ++ Q.SPEC_TAC (`2n ** n`, `k`)
       ++ RW_TAC arith_ss
          [GSYM posreal_of_num_mul, preal_div_def, inv_mul, entire,
           posreal_of_num_inj]
       ++ Know `!x. x = inv (2 * 3 * & k) * (2 * 3 * & k * x)`
       >> RW_TAC posreal_ss [GSYM mul_assoc, mul_linv, entire, mul_eq_infty]
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ MATCH_MP_TAC le_lmul_imp
       ++ RW_TAC std_ss [mul_assoc]
       ++ RW_TAC posreal_ss
          [add_ldistrib, mul_rinv, sub_ldistrib, inv_eq_infty, mul_eq_infty]
       ++ RW_TAC std_ss [GSYM posreal_of_num_mul]
       ++ CONV_TAC (ONCE_DEPTH_CONV permute_mul_conv)
       ++ RW_TAC posreal_ss [mul_rinv, mul_rinv2],
       POP_ASSUM_LIST (K ALL_TAC)
       ++ Q.SPEC_TAC (`Num (s "n")`, `k`)
       ++ Cases
       ++ RW_TAC arith_ss [EXP, ADD1]
       ++ RW_TAC arith_ss
          [preal_div_def, mul_assoc, posreal_of_num_inj,
           GSYM posreal_of_num_mul, inv_mul, entire, EXP_EQ_0]
       ++ RW_TAC posreal_ss
          [sub_ldistrib, inv_eq_infty, mul_eq_infty, add_ldistrib]
       ++ Know `!x. x = inv (2 * 3 * & (2 ** n)) * ((2 * 3 * & (2 ** n)) * x)`
       >> (Suff `inv (2 * 3 * & (2 ** n)) * (2 * 3 * & (2 ** n)) = 1`
           >> RW_TAC posreal_ss [GSYM mul_assoc]
           ++ MATCH_MP_TAC mul_linv
           ++ RW_TAC posreal_ss [entire, mul_eq_infty, EXP_EQ_0])
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ MATCH_MP_TAC le_lmul_imp
       ++ RW_TAC std_ss [mul_assoc]
       ++ RW_TAC posreal_ss
          [sub_ldistrib, inv_eq_infty, mul_eq_infty, add_ldistrib]
       ++ RW_TAC std_ss [GSYM posreal_of_num_mul]
       ++ CONV_TAC (ONCE_DEPTH_CONV permute_mul_conv)
       ++ RW_TAC posreal_ss [mul_rinv, mul_rinv2, EXP_EQ_0],
       RW_TAC posreal_reduce_ss [],
       RW_TAC posreal_reduce_ss [],
       Know `s "n" = 0` >> COOPER_TAC
       ++ RW_TAC posreal_reduce_ss [NUM_OF_INT],
       Know `s "n" = 0` >> COOPER_TAC
       ++ RW_TAC posreal_reduce_ss [NUM_OF_INT],
       POP_ASSUM_LIST (K ALL_TAC)
       ++ Q.SPEC_TAC (`Num (s "i")`, `k`)
       ++ RW_TAC arith_ss
          [preal_div_def, mul_assoc, posreal_of_num_inj,
           GSYM posreal_of_num_mul, inv_mul, entire, EXP_EQ_0]
       ++ RW_TAC posreal_ss
          [sub_ldistrib, inv_eq_infty, mul_eq_infty, add_ldistrib]
       ++ Know `!x. x = inv (3 * & (2 ** k)) * ((3 * & (2 ** k)) * x)`
       >> (Suff `inv (3 * & (2 ** k)) * (3 * & (2 ** k)) = 1`
           >> RW_TAC posreal_ss [GSYM mul_assoc]
           ++ MATCH_MP_TAC mul_linv
           ++ RW_TAC posreal_ss [entire, mul_eq_infty, EXP_EQ_0])
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ MATCH_MP_TAC le_lmul_imp
       ++ RW_TAC posreal_ss
          [sub_ldistrib, inv_eq_infty, mul_eq_infty, add_ldistrib]
       ++ RW_TAC std_ss [GSYM posreal_of_num_mul]
       ++ CONV_TAC (ONCE_DEPTH_CONV permute_mul_conv)
       ++ RW_TAC posreal_ss [mul_rinv, mul_rinv2, EXP_EQ_0]]);

(*
val rabin_terminates = Count.apply prove
  (``wp rabin One = One``,
*)
