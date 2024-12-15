open HolKernel Parse boolLib bossLib;

open metisLib arithmeticTheory pred_setTheory
     pred_setLib stringLib listTheory state_transformerTheory
     extra_numTheory combinTheory
     pairTheory realTheory realLib jrhUtils
     realSimps numTheory simpLib seqTheory subtypeTheory
     transcTheory limTheory stringTheory rich_listTheory stringSimps listSimps
     informationTheory leakageTheory leakageLib wordsTheory wordsLib;

open extra_boolTheory extra_pred_setTheory extra_realTheory extra_listTheory
     extra_stringTheory extra_stringLib;

open real_sigmaTheory;

open hurdUtils util_probTheory real_measureTheory real_lebesgueTheory
     real_probabilityTheory;

val _ = new_theory "basic_leakage_examples";
val _ = temp_set_fixity "CROSS" (Infixl 600)

val safe_set_ss = (simpLib.++ (bool_ss, PRED_SET_ss));

val set_ss = (simpLib.++ (arith_ss, PRED_SET_ss));

val list_string_ss = (simpLib.++ (list_ss, STRING_ss));

fun TRY2_TAC t1 t2 state = let
 val (a1,f1) = t1 state handle HOL_ERR _ => ALL_TAC state
 in if length a1 = 0 then (a1,f1) else t2 state end;


Triviality lem1:
  !(s:string) (n:num) (m:num).
    ((\s'. (if s' = s then n else 0)) = (\s'. (if s' = s then m else 0))) =
    (n = m)
Proof METIS_TAC []
QED

Triviality lem2:
  !(s:string) (n:num). ((\s'. (if s' = s then n else 0)) = (\s'. 0)) = (n = 0)
Proof METIS_TAC []
QED

Triviality lem3:
  !(s:string) (n:num). ((\s'. 0) = (\s'. (if s' = s then n else 0))) = (n = 0)
Proof METIS_TAC []
QED

Triviality lem4:
  !(n1:num)(n2:num)(m1:num)(m2:num).
    ((\s'. (if s' = "h2" then m1 else (if s' = "h1" then n1 else 0))) =
     (\s'. (if s' = "h2" then m2 else (if s' = "h1" then n2 else 0)))) =
    ((n1=n2) /\ (m1=m2))
Proof
  REPEAT STRIP_TAC >> EQ_TAC
  >- (ONCE_REWRITE_TAC [FUN_EQ_THM]
      >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
      >> Cases_on ‘n1 = n2’
      >- (Q.PAT_X_ASSUM ‘!x. (if x = "h2" then m1 else
                                (if x = "h1" then n1 else 0)) =
                             (if x = "h2" then m2 else
                                (if x = "h1" then n2 else 0))’
          (MP_TAC o Q.SPEC ‘"h2"’) >> RW_TAC std_ss [])
      >> Q.PAT_X_ASSUM ‘!x. (if x = "h2" then m1 else
                               (if x = "h1" then n1 else 0)) =
                            (if x = "h2" then m2 else
                               (if x = "h1" then n2 else 0))’
          (MP_TAC o Q.SPEC ‘"h1"’) >> SRW_TAC [] [])
  >> RW_TAC std_ss []
QED

Triviality lem5:
  !(m1:num)(m2:num)(n2:num).
    ((\s'. (if s' = "h2" then m1 else 0)) =
     (\s'. (if s' = "h2" then m2 else (if s' = "h1" then n2 else 0)))) =
    ((n2=0) /\ (m1=m2))
Proof
  REPEAT STRIP_TAC >> EQ_TAC
  >- (ONCE_REWRITE_TAC [FUN_EQ_THM]
      >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
      >> Cases_on ‘n2=0’
      >- (Q.PAT_X_ASSUM ‘!x. (if x = "h2" then m1 else 0) =
                             (if x = "h2" then m2 else
                                (if x = "h1" then n2 else 0))’
          (MP_TAC o Q.SPEC ‘"h2"’) >> RW_TAC std_ss [])
      >> Q.PAT_X_ASSUM ‘!x. (if x = "h2" then m1 else 0) =
                            (if x = "h2" then m2 else
                               (if x = "h1" then n2 else 0))’
          (MP_TAC o Q.SPEC ‘"h1"’) >> SRW_TAC [] [])
  >> RW_TAC std_ss []
QED

Triviality lem6:
  !(n:num)(m:num).
    ((\s'. (if s' = "h2" then m else (if s' = "h1" then n else 0))) =
     (\s'. 0)) =
    ((n=0) /\ (m=0))
Proof
  REPEAT STRIP_TAC >> EQ_TAC
  >- (ONCE_REWRITE_TAC [FUN_EQ_THM]
      >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
      >> Cases_on ‘n = 0’
      >- (Q.PAT_X_ASSUM ‘!x. (if x = "h2" then m else
                                (if x = "h1" then n else 0)) = 0’
          (MP_TAC o Q.SPEC ‘"h2"’) >> RW_TAC std_ss [])
      >> Q.PAT_X_ASSUM ‘!x. (if x = "h2" then m else
                               (if x = "h1" then n else 0)) = 0’
          (MP_TAC o Q.SPEC ‘"h1"’) >> SRW_TAC [] [])
  >> RW_TAC std_ss []
QED

Triviality lem7:
  !(s:string) (n:num) (m:num). ((\s'. (if s' = s then [n] else [])) =
                                (\s'. (if s' = s then [m] else []))) =
                               (n = m)
Proof
  REPEAT STRIP_TAC >> EQ_TAC
  >- (RW_TAC list_ss [FUN_EQ_THM] >> POP_ASSUM (MP_TAC o Q.SPEC ‘s’)
      >> RW_TAC std_ss [])
  >> RW_TAC std_ss []
QED

Triviality lem8:
  !(n1:num) (n2:num) (n3:num) (m1:num) (m2:num) (m3:num).
    ((\s'. (if (s' = "out") then [n1;n2] else
              (if (s' = "low") then [n3] else []))) =
     (\s'. (if (s' = "out") then [m1;m2] else
              (if (s' = "low") then [m3] else [])))) =
    ((n1 = m1) /\ (n2 = m2) /\ (n3 = m3))
Proof
  REPEAT STRIP_TAC >> EQ_TAC
  >- (RW_TAC list_ss [FUN_EQ_THM]
      >| [POP_ASSUM (MP_TAC o Q.SPEC ‘"out"’) >> RW_TAC std_ss [],
          POP_ASSUM (MP_TAC o Q.SPEC ‘"out"’) >> RW_TAC std_ss [],
          POP_ASSUM (MP_TAC o Q.SPEC ‘"low"’) >> RW_TAC string_ss []])
  >> RW_TAC std_ss []
QED

(* *************************** *)
(* Example 1: out = high + low *)
(* TOTAL LEAKAGE               *)
(* *************************** *)

Definition high:
  (high 0 = {(\s:string. if s = "high" then 0 else 0)}) /\
  (high (SUC n) = (\s:string. if s = "high" then SUC n else 0)INSERT(high n))
End

Definition low:
  (low 0 = {(\s:string. if s = "low" then 0 else 0)}) /\
  (low (SUC n) = (\s:string. if s = "low" then SUC n else 0)INSERT(low n))
End

Definition random: random = {(\s:string. (0:num))}
End

Definition M1:
  M1 = (\s: ((num,num,num) prog_state).
         (\s':string. if (s' = "out") then (H s "high") + (L s "low") else 0))
End

val example1_conv = SIMP_CONV arith_ss [high, low, random, lem1, lem2, lem3];

Theorem leakage_example1:
    leakage (unif_prog_space (high (SUC (SUC (SUC 0))))
                             (low (SUC (SUC (SUC 0)))) random) M1 = 2
Proof
  CONV_TAC (LAND_CONV
            (LEAKAGE_COMPUTE_CONV (“high (SUC (SUC (SUC 0)))”,
                                   “low (SUC (SUC (SUC 0)))”,
                                   “random”)
             [high, low, random, lem1, lem2, lem3]
             [M1, H_def, L_def, FST, SND]
             example1_conv example1_conv example1_conv
             example1_conv example1_conv example1_conv example1_conv))
  >> SIMP_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER]
  >> ‘lg 4 = 2’
    by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >>
        RW_TAC std_ss [lg_pow])
  >> RW_TAC real_ss []
  >> ONCE_REWRITE_TAC [REAL_MUL_COMM] >> RW_TAC std_ss [GSYM real_div]
  >> (MP_TAC o Q.SPECL [‘32’,‘2’,‘16’]) REAL_EQ_LDIV_EQ
  >> RW_TAC real_ss []
QED

(* ******************************** *)
(* Example 2:    out = high XOR low *)
(* TOTAL LEAKAGE                    *)
(* ******************************** *)

Definition M2:
  M2 = λ(s: ((num,num,num) prog_state)) (s':string).
         if (s' = "out") then
           w2n (((n2w (H s "high")):word2) ?? (n2w (L s "low")))
         else 0
End

val example2_output_conv =
  SIMP_CONV arith_ss [lem1,lem2,lem3, w2n_11] THENC
  FIND_CONV “w2n(a ?? b)” WORD_EVAL_CONV;

val example2_input_conv = SIMP_CONV arith_ss [high, low, random, lem1,lem2,lem3];

Theorem leakage_example2:
  leakage (unif_prog_space (high (SUC (SUC (SUC 0))))
           (low (SUC (SUC (SUC 0)))) random) M2 = 2
Proof
  CONV_TAC (LAND_CONV
            (LEAKAGE_COMPUTE_CONV (“high (SUC (SUC (SUC 0)))”,
                                   “low (SUC (SUC (SUC 0)))”,
                                   “random”)
             [high, low, random, lem1, lem2, lem3, w2n_11]
             [M2, H_def, L_def, FST, SND]
             example2_input_conv example2_input_conv example2_input_conv
             example2_input_conv example2_input_conv example2_input_conv
             example2_output_conv))
  >> SIMP_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER]
  >> ‘lg 4 = 2’
    by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >>
        RW_TAC std_ss [lg_pow])
  >> RW_TAC real_ss []
  >> ONCE_REWRITE_TAC [REAL_MUL_COMM] >> RW_TAC std_ss [GSYM real_div]
  >> (MP_TAC o Q.SPECL [‘32’,‘2’,‘16’]) REAL_EQ_LDIV_EQ
  >> RW_TAC real_ss []
QED

(* ********************************** *)
(* Example 3:  out = h1 XOR h2        *)
(* 2 BITS: match of bits of h1 and h2 *)
(* ********************************** *)

val h1 = Define
   ‘(h1 0 = {(\s:string. if s = "h1" then 0 else 0)}) /\
    (h1 (SUC n) = (\s:string. if s = "h1" then SUC n else 0)INSERT(h1 n))’;

val h2 = Define
   ‘(h2 l 0 = IMAGE (\s: num state. (\s':string. if s' = "h2" then 0 else s s')) l) /\
    (h2 l (SUC n) = (IMAGE (\s: num state. (\s':string. if s' = "h2" then (SUC n) else s s')) l) UNION
                    (h2 l n))’;

Definition high[allow_rebind]: high n = h2 (h1 n) n
End

Definition low[allow_rebind]: low = {(\s:string. (0:num))}
End

Definition random[allow_rebind]: random = {(\s:string. (0:num))}
End

val M3 = Define
   ‘M3 = (\s: ((num,num,num) prog_state). (\s':string. if (s' = "out")
                then w2n (((n2w (H s "h1")):word2) ?? (n2w (H s "h2"))) else 0))’;

val example3_output_conv = SIMP_CONV string_ss [lem1, lem2, lem3, lem4, lem5, lem6, w2n_11]
                           THENC (TRY_CONV (FIND_CONV “(x:string)=(y:string)” string_EQ_CONV))
                           THENC (TRY_CONV (FIND_CONV “w2n(a ?? b)” WORD_EVAL_CONV));

val example3_h_conv = SIMP_CONV arith_ss [lem1, lem2, lem3, lem4, lem5, lem6, w2n_11]
                          THENC (TRY_CONV (FIND_CONV “(a ?? b) = (c ?? d)” WORD_EVAL_CONV));

val example3_lr_conv = SIMP_CONV arith_ss [lem1, lem2, lem3, lem4, lem5, lem6];

val example3_h_input_conv = SIMP_CONV set_ss [high, h1, h2]
THENC  (FIND_CONV “x UNION y”
                        (UNION_CONV (SIMP_CONV set_ss [lem1, lem2, lem3, lem4, lem5, lem6])));

val example3_lr_input_conv = SIMP_CONV set_ss [low, random];

val leakage_example3 = store_thm
  ("leakage_example3",
   “leakage (unif_prog_space (high (SUC (SUC (SUC 0)))) low random) M3 = 2”,
CONV_TAC (RATOR_CONV (RAND_CONV (LEAKAGE_COMPUTE_CONV (“high (SUC (SUC (SUC 0)))”,
                              “low”,
                              “random”)
                        [high, low, random, h1, h2, lem1, lem2, lem3, lem4, lem5, lem6, w2n_11]
                        [M3, H_def, L_def, FST, SND, w2n_11]
                        example3_h_input_conv example3_lr_input_conv example3_lr_input_conv
                        example3_h_conv example3_lr_conv example3_lr_conv
                        example3_output_conv)))
>> RW_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER, lg_mul, lg_2]
>> ‘lg 4 = 2’
        by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> ‘lg 16 = 4’
        by (‘16 = 2 pow 4’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> ONCE_REWRITE_TAC [REAL_MUL_COMM]
>> RW_TAC real_ss [GSYM real_div]);

(* *************************** *)
(* Example 4:    out = h1 + h2 *)
(* PARTIAL LEAKAGE             *)
(* *************************** *)

val M4 = Define
   ‘M4 = (\s: ((num,num,num) prog_state). (\s':string. if (s' = "out")
   then (H s "h1") + (H s "h2") else 0))’;

val example4_output_conv = SIMP_CONV string_ss [lem1, lem2, lem3, lem4, lem5, lem6]
                           THENC (TRY_CONV (FIND_CONV “(x:string)=(y:string)” string_EQ_CONV));

val example4_dup_conv = SIMP_CONV arith_ss [lem1, lem2, lem3, lem4, lem5, lem6];

val example4_h_input_conv = SIMP_CONV set_ss [high, h1, h2]
THENC  (FIND_CONV “x UNION y”
                        (UNION_CONV (SIMP_CONV set_ss [lem1, lem2, lem3, lem4, lem5, lem6])));

val example4_lr_input_conv = SIMP_CONV set_ss [low, random];

val leakage_example4 = store_thm
  ("leakage_example4",
   “leakage (unif_prog_space ((high (SUC (SUC (SUC 0))))) low random) M4 = inv 16 * (52 - 6 * lg 3)”,
CONV_TAC (RATOR_CONV (RAND_CONV (LEAKAGE_COMPUTE_CONV (“high (SUC (SUC (SUC 0)))”,
                              “low”,
                              “random”)
                        [high, low, random, h1, h2, lem1, lem2, lem3, lem4, lem5, lem6]
                        [M4, H_def, L_def, FST, SND, w2n_11]
                        example4_h_input_conv example4_lr_input_conv example4_lr_input_conv
                        example4_dup_conv example4_dup_conv example4_dup_conv
                        example4_output_conv)))
>> RW_TAC real_ss [lg_1, lg_mul, lg_2, lg_inv, GSYM REAL_INV_1OVER, real_div]
>> ‘lg 8 = 3’ by (‘8 = 2 pow 3’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> ‘lg 4 = 2’ by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> ‘lg 16 = 4’ by (‘16 = 2 pow 4’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> RW_TAC real_ss [REAL_INV_EQ_0]
>> REPEAT (POP_ASSUM (K ALL_TAC))
>> REAL_ARITH_TAC);

(* *************************** *)
(* Example 5:  intermed. leak  *)
(* No leakage                  *)
(* *************************** *)

Definition assign1[allow_rebind]:
  assign1 = (\s: ((num,num,num) prog_state).
               (\s':string. if (s' = "out")
                            then (H s "high") else 0))
End

Definition assign2[allow_rebind]:
  assign2 = (\s: ((num,num,num) prog_state).
               (\s':string. if (s' = "out")
                            then (L s "low") else 0))
End

val M5 = Define
   ‘M5 = (\s: ((num,num,num) prog_state). assign2 ((H s, assign1 s), R s))’;

Definition high[allow_rebind]:
   (high 0 = {(\s:string. if s = "high" then 0 else 0)}) /\
   (high (SUC n) = (\s:string. if s = "high" then SUC n else 0)INSERT(high n))
End

Definition low[allow_rebind]:
  (low 0 = {(\s:string. if s = "low" then 0 else 0)}) /\
  (low (SUC n) = (\s:string. if s = "low" then SUC n else 0)INSERT(low n))
End

Definition random[allow_rebind]: random = {(\s:string. (0:num))}
End

val example5_conv = SIMP_CONV arith_ss [high, low, random, lem1,lem2,lem3];

val example5_output_conv = SIMP_CONV arith_ss [high, low, random, lem1,lem2,lem3]
                           THENC (TRY_CONV (FIND_CONV “(x:string)=(y:string)” string_EQ_CONV));

val leakage_example5 = store_thm
  ("leakage_example5",
   “leakage (unif_prog_space (high (SUC (SUC (SUC 0)))) (low (SUC (SUC (SUC 0)))) random) M5 = 0”,
CONV_TAC (RATOR_CONV (RAND_CONV (LEAKAGE_COMPUTE_CONV (“high (SUC (SUC (SUC 0)))”,
                              “low (SUC (SUC (SUC 0)))”,
                              “random”)
                        [high, low, random, lem1, lem2, lem3]
                        [M5, assign1, assign2, H_def, L_def, FST, SND]
                        example5_conv example5_conv example5_conv

                        example5_conv example5_conv example5_conv
                        example5_output_conv)))
>> RW_TAC real_ss [REAL_DIV_REFL, lg_1]);

(* *************************** *)
(* Example 5': intermed. leak  *)
(* total leakage               *)
(* *************************** *)

Definition state_update_def:
   state_update name value =
   (\s:(num list) state. (\n:string. if (n=name) then value else s n))
End
val state_update = state_update_def

Definition state_append:
   state_append name value =
   λs:(num list) state.
     state_update name ((if (value=[]) then [] else [HD value]) ++ s name) s
End

Definition assign1[allow_rebind]:
  assign1 = (\s: ((num list,num list,num list) prog_state).
               state_update "out" (H s "high") (L s))
End

Definition assign2[allow_rebind]:
  assign2 = (λs: ((num list,num list,num list) prog_state).
               state_append "out" (L s "low") (L s))
End

val M5' = Define
   ‘M5' = (\s: ((num list,num list,num list) prog_state). assign2 ((H s, assign1 s), R s))’;

Definition high[allow_rebind]:
  (high 0 = {(\s:string. if s = "high" then [0] else [])}) /\
  (high (SUC n) = (\s:string. if s = "high" then [SUC n] else [])INSERT(high n))
End

Definition low[allow_rebind]:
  (low 0 = {(\s:string. if s = "low" then [0] else [])}) /\
  (low (SUC n) = (\s:string. if s = "low" then [SUC n] else [])INSERT(low n))
End

Definition random[allow_rebind]:
  random = {(\s:string. ([]:num list))}
End

val example5'_conv = SIMP_CONV list_string_ss [high, low, random, lem7, lem8, APPEND, PAIR_EQ];

val example5'_output_conv = SIMP_CONV list_string_ss [high, low, random, lem7, lem8, APPEND, PAIR_EQ]
                            THENC (TRY_CONV (FIND_CONV “(x:string)=(y:string)” string_EQ_CONV))
                            THENC SIMP_CONV list_string_ss [high, low, random, lem7, lem8, APPEND];

val leakage_example5' = store_thm
  ("leakage_example5'",
   “leakage (unif_prog_space (high (SUC (SUC (SUC 0)))) (low (SUC (SUC (SUC 0)))) random) M5' = 2”,
PURE_REWRITE_TAC [M5', state_update, state_append, assign1, assign2]
>> CONV_TAC (RATOR_CONV (RAND_CONV (LEAKAGE_COMPUTE_CONV (“high (SUC (SUC (SUC 0)))”,
                              “low (SUC (SUC (SUC 0)))”,
                              “random”)
                        [high, low, random, lem7, lem8, APPEND]
                        [H_def, L_def, FST, SND, APPEND]
                        example5'_conv example5'_conv example5'_conv
                        example5'_output_conv example5'_output_conv example5'_output_conv
                        example5'_output_conv)))
>> RW_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER]
>> ‘lg 4 = 2’ by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> RW_TAC real_ss []
>> ONCE_REWRITE_TAC [REAL_MUL_COMM] >> RW_TAC std_ss [GSYM real_div]
>> (MP_TAC o Q.SPECL [‘32’,‘2’,‘16’]) REAL_EQ_LDIV_EQ
>> RW_TAC real_ss []);

(* *********************************** *)
(* Example 8:    out = high XOR random *)
(* NO LEAKAGE (hidden prob)            *)
(* *********************************** *)

Definition high[allow_rebind]:
  (high 0 = {(\s:string. if s = "high" then 0 else 0)}) /\
  (high (SUC n) = (\s:string. if s = "high" then SUC n else 0)INSERT(high n))
End

Definition random[allow_rebind]:
  (random 0 = {(\s:string. if s = "random" then 0 else 0)}) /\
  (random (SUC n) = (\s:string. if s = "random" then SUC n else 0) INSERT
                    random n)
End

Definition low[allow_rebind]: low = {(\s:string. (0:num))}
End

val M8 = Define
   ‘M8 = (\s: ((num,num,num) prog_state). (\s':string. if (s' = "out")
        then w2n (((n2w (H s "high")):word2) ?? (n2w (R s "random"))) else 0))’;

val example8_conv = SIMP_CONV arith_ss [high, low, random, lem1, lem2, lem3, w2n_11];

val example8_output_conv = SIMP_CONV arith_ss [high, low, random, lem1, lem2, lem3, w2n_11]
                            THENC (TRY_CONV (FIND_CONV “(x:string)=(y:string)” string_EQ_CONV))
                            THENC (TRY_CONV (FIND_CONV “w2n(a ?? b)” WORD_EVAL_CONV))
                            THENC SIMP_CONV arith_ss [high, low, random, lem1, lem2, lem3, w2n_11];

val leakage_example8 = store_thm
  ("leakage_example8",
   “leakage (unif_prog_space (high (SUC (SUC (SUC 0)))) low (random (SUC (SUC (SUC 0))))) M8 = 0”,
CONV_TAC (RATOR_CONV (RAND_CONV (LEAKAGE_COMPUTE_CONV (“high (SUC (SUC (SUC 0)))”,
                              “low”,
                              “random (SUC (SUC (SUC 0)))”)
                        [high, low, random, lem1,lem2]
                        [M8, H_def, R_def, FST, SND, lem1,lem2, lem3]
                        example8_conv example8_conv example8_conv
                        example8_output_conv example8_conv example8_output_conv
                        example8_output_conv)))
>> RW_TAC real_ss [lg_mul, lg_2, lg_1, lg_inv, GSYM REAL_INV_1OVER]
>> ‘lg 4 = 2’
        by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> ‘lg 16 = 4’
        by (‘16 = 2 pow 4’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> ONCE_REWRITE_TAC [REAL_MUL_COMM]
>> RW_TAC real_ss [GSYM real_div]);

(* *********************************** *)
(* Example 8':   out = high XOR random *)
(* TOTAL LEAKAGE (visible prob)        *)
(* *********************************** *)

val high_thm = prove
   (“!n. high n = if (n=0) then
                {(\s:string. if s = "high" then 0 else 0)}
             else
                (\s:string. if s = "high" then n else 0)INSERT(high (n-1))”,
     Induct >> RW_TAC arith_ss [high]);

val random_thm = prove
   (“!n. random n = if (n=0) then
                {(\s:string. if s = "random" then 0 else 0)}
             else
                (\s:string. if s = "random" then n else 0)INSERT(random (n-1))”,
     Induct >> RW_TAC arith_ss [random]);

val leakage_example8' = store_thm
  ("leakage_example8'",
   “visible_leakage (unif_prog_space (high 3) low (random 3)) M8 = 2”,
‘FINITE (high 3)’
   by (NTAC 4 (ONCE_REWRITE_TAC [high_thm])
       >> RW_TAC set_ss [])
>> ‘FINITE (random 3)’
   by (NTAC 4 (ONCE_REWRITE_TAC [random_thm])
       >> RW_TAC set_ss [])
>> ‘FINITE (low)’ by RW_TAC set_ss [low]
>> ‘~ ((high 3) CROSS low CROSS (random 3) = {})’
        by (RW_TAC std_ss [Once EXTENSION]
            >> NTAC 4 (ONCE_REWRITE_TAC [high_thm, random_thm, low])
            >> RW_TAC set_ss []
            >> Q.EXISTS_TAC ‘(((\s.0),(\s.0)),(\s.0))’
            >> RW_TAC std_ss [])
>> ASM_SIMP_TAC std_ss
   [unif_prog_space_visible_leakage_computation_reduce]
>> NTAC 4 (ONCE_REWRITE_TAC [high_thm, random_thm, low])
>> RW_TAC set_ss [CROSS_EQNS, lem1, lem2]
>> CONV_TAC (FIND_CONV “x UNION y” (UNION_CONV (SIMP_CONV set_ss [lem1,lem2])))
>> RW_TAC set_ss [CROSS_EQNS, lem1, lem2, M8, H_def, R_def]
>> CONV_TAC (FIND_CONV “x UNION y”
                        (UNION_CONV (SIMP_CONV set_ss [lem1,lem2, w2n_11]
                                     THENC (FIND_CONV “(a ?? b) = (c ?? d)” WORD_EVAL_CONV))))
>> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                      THENC (FIND_CONV “x DELETE y”
                                        (DELETE_CONV (SIMP_CONV arith_ss [PAIR_EQ,lem1,lem2,lem3, w2n_11]
                                                      THENC (FIND_CONV “(a ?? b) = (c ?? d)”
                                                                        WORD_EVAL_CONV))))
                      THENC (SIMP_CONV arith_ss [lem1,lem2,lem3, w2n_11]))
             THENC (FIND_CONV “(a ?? b) = (c ?? d)” WORD_EVAL_CONV))
>> RW_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER]
>> ‘lg 4 = 2’
        by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> ONCE_REWRITE_TAC [REAL_MUL_COMM]
>> RW_TAC real_ss [GSYM real_div]);

(* *********************************** *)

val flip_example_lem = prove
  (“!(s:string). ~((\s'. s' = s) = (\s'. F))”,METIS_TAC []);

val M = Define
   ‘M = (\s: ((bool,bool,bool) prog_state). (\s':string. if (s' = "out")
   then (if (R s "r") then (L s "l") else (H s "h")) else F))’;

val hidden_flip_example = store_thm
  ("hidden_flip_example",
   “leakage (unif_prog_space {(\s:string. s = "h");(\s:string.F)}
                              {(\s:string. s = "l");(\s:string.F)}
                              {(\s:string. s = "r");(\s:string.F)}) M = 3/2 - (3 * lg 3)/4”,
‘~ ({(\s:string. s = "h");(\s:string.F)} CROSS
        {(\s:string. s = "l");(\s:string.F)} CROSS
        {(\s:string. s = "r");(\s:string.F)} = {})’
        by (RW_TAC set_ss [Once EXTENSION]
            >> Q.EXISTS_TAC ‘(((\s.F),(\s.F)),(\s.F))’
            >> RW_TAC std_ss [])
>> ASM_SIMP_TAC set_ss
   [unif_prog_space_leakage_computation_reduce]
>> RW_TAC set_ss [CROSS_EQNS, lem1, flip_example_lem]
>> CONV_TAC (FIND_CONV “x UNION y” (UNION_CONV (SIMP_CONV set_ss [flip_example_lem, lem1])))
>> RW_TAC set_ss [CROSS_EQNS, lem1, M, H_def, L_def, R_def]
>> CONV_TAC (FIND_CONV “x UNION y” (UNION_CONV (SIMP_CONV set_ss [flip_example_lem, lem1])))
>> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                      THENC (FIND_CONV “x DELETE y”
                                        (DELETE_CONV (SIMP_CONV arith_ss [PAIR_EQ, flip_example_lem])))
                      THENC SIMP_CONV arith_ss [flip_example_lem]))
>> SIMP_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER, lg_2, REAL_MUL_LINV]
>> ‘lg 4 = 2’
        by (‘4 = 2 pow 2’ by RW_TAC real_ss [pow] >> POP_ORW >> RW_TAC std_ss [lg_pow])
>> RW_TAC real_ss [lg_mul, REAL_INV_POS, lg_inv]
>> Q.ABBREV_TAC ‘foo = 3 * lg 3’
>> ‘3 * (~2 + lg 3) + (~2 + 3 * (~2 + lg 3)) =
    ~14 + 2 * foo’
        by (Q.UNABBREV_TAC ‘foo’ >> REAL_ARITH_TAC)
>> POP_ORW
>> RW_TAC real_ss [REAL_ADD_ASSOC, real_sub, REAL_NEG_ADD]
>> ONCE_REWRITE_TAC [REAL_MUL_COMM]
>> RW_TAC std_ss [GSYM real_div]
>> (MP_TAC o Q.SPECL [‘(12 + ~(2 * foo))’,‘3 / 2 + ~foo / 4’,‘8’]) REAL_EQ_LDIV_EQ
>> RW_TAC real_ss [REAL_ADD_RDISTRIB]
>> RW_TAC std_ss [real_div, Once (GSYM REAL_MUL_ASSOC)]
>> ‘inv 4 * 8 = 2’ by (ONCE_REWRITE_TAC [REAL_MUL_COMM] >> RW_TAC real_ss [GSYM real_div])
>> POP_ORW
>> REAL_ARITH_TAC);


val visible_flip_example = store_thm
  ("visible_flip_example",
   “visible_leakage (unif_prog_space {(\s:string. s = "h");(\s:string.F)}
                              {(\s:string. s = "l");(\s:string.F)}
                              {(\s:string. s = "r");(\s:string.F)}) M = 1/2”,
‘~ ({(\s:string. s = "h");(\s:string.F)} CROSS
        {(\s:string. s = "l");(\s:string.F)} CROSS
        {(\s:string. s = "r");(\s:string.F)} = {})’
        by (RW_TAC set_ss [Once EXTENSION]
            >> Q.EXISTS_TAC ‘(((\s.F),(\s.F)),(\s.F))’
            >> RW_TAC std_ss [])
>> ASM_SIMP_TAC set_ss
   [unif_prog_space_visible_leakage_computation_reduce]
>> RW_TAC set_ss [CROSS_EQNS, flip_example_lem]
>> CONV_TAC (FIND_CONV “x UNION y” (UNION_CONV (SIMP_CONV set_ss [flip_example_lem])))
>> RW_TAC set_ss [CROSS_EQNS, lem1, M, H_def, L_def, R_def]
>> CONV_TAC (FIND_CONV “x UNION y” (UNION_CONV (SIMP_CONV set_ss [flip_example_lem])))
>> CONV_TAC (REPEATC (SIMP_CONV set_ss [REAL_SUM_IMAGE_THM]
                      THENC (FIND_CONV “x DELETE y”
                                        (DELETE_CONV (SIMP_CONV arith_ss [PAIR_EQ, flip_example_lem])))
                      THENC SIMP_CONV arith_ss [flip_example_lem]))
>> SIMP_TAC real_ss [lg_1, lg_inv, GSYM REAL_INV_1OVER, lg_2, REAL_MUL_LINV]
>> ONCE_REWRITE_TAC [REAL_MUL_COMM] >> RW_TAC real_ss [GSYM real_div, REAL_INV_1OVER]);
val _ = export_theory ();
