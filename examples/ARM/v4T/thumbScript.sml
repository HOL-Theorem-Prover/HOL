(* ========================================================================= *)
(* FILE          : arm_evalScript.sml                                        *)
(* DESCRIPTION   : Various theorems about the ISA and instruction encoding   *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005-2007                                                 *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setSimps", "rich_listTheory", "wordsLib", "wordsSyntax",
            "armLib", "instructionTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q arithmeticTheory wordsLib wordsTheory bitTheory;
open combinTheory updateTheory armTheory instructionTheory;

val _ = new_theory "thumb";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val _ = wordsLib.guess_lengths();

(* ------------------------------------------------------------------------- *)

val the_goal =
 ``THUMB_TO_ARM (enc_ i) = enc
   (case i of
       LSL_1 Rd Rm imm5 ->
         MOV AL T (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) imm5)
    || LSR_1 Rd Rm imm5 ->
         MOV AL T (w2w Rd) (Dp_shift_immediate (LSR (w2w Rm)) imm5)
    || ASR_1 Rd Rm imm5 ->
         MOV AL T (w2w Rd) (Dp_shift_immediate (ASR (w2w Rm)) imm5)
    || ADD_3 Rd Rn Rm ->
         ADD AL T (w2w Rd) (w2w Rn) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || SUB_3 Rd Rn Rm ->
         SUB AL T (w2w Rd) (w2w Rn) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || ADD_1 Rd Rn imm3 ->
         ADD AL T (w2w Rd) (w2w Rn) (Dp_immediate 0w (w2w imm3))
    || SUB_1 Rd Rn imm3 ->
         SUB AL T (w2w Rd) (w2w Rn) (Dp_immediate 0w (w2w imm3))
    || MOV_1 Rd imm8 ->
         MOV AL T (w2w Rd) (Dp_immediate 0w imm8)
    || CMP_1 Rn imm8 ->
         CMP AL (w2w Rn) (Dp_immediate 0w imm8)
    || ADD_2 Rd imm8 ->
         ADD AL T (w2w Rd) (w2w Rd) (Dp_immediate 0w imm8)
    || SUB_2 Rd imm8 ->
         SUB AL T (w2w Rd) (w2w Rd) (Dp_immediate 0w imm8)
    || AND_  Rd Rm ->
         AND AL T (w2w Rd) (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || EOR_  Rd Rm ->
         EOR AL T (w2w Rd) (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || LSL_2 Rd Rm ->
         MOV AL T (w2w Rd) (Dp_shift_register (LSL (w2w Rd)) (w2w Rm))
    || LSR_2 Rd Rm ->
         MOV AL T (w2w Rd) (Dp_shift_register (LSR (w2w Rd)) (w2w Rm))
    || ASR_2 Rd Rm ->
         MOV AL T (w2w Rd) (Dp_shift_register (ASR (w2w Rd)) (w2w Rm))
    || ADC_  Rd Rm ->
         ADC AL T (w2w Rd) (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || SBC_  Rd Rm ->
         SBC AL T (w2w Rd) (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || ROR_  Rd Rm ->
         MOV AL T (w2w Rd) (Dp_shift_register (ROR (w2w Rd)) (w2w Rm))
    || TST_  Rd Rm ->
         TST AL (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || NEG_  Rd Rm ->
         RSB AL T (w2w Rd) (w2w Rm) (Dp_immediate 0w 0w)
    || CMP_2 Rd Rm ->
         CMP AL (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || CMN_  Rd Rm ->
         CMN AL (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || ORR_  Rd Rm ->
         ORR AL T (w2w Rd) (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || MUL_  Rd Rm ->
         MUL AL T (w2w Rd) (w2w Rm) (w2w Rd)
    || BIC_  Rd Rm ->
         BIC AL T (w2w Rd) (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || MVN_  Rd Rm ->
         MVN AL T (w2w Rd) (Dp_shift_immediate (LSL (w2w Rm)) 0w)
    || ADD_4 H1Rd H2Rm ->
         ADD AL F H1Rd H1Rd (Dp_shift_immediate (LSL H2Rm) 0w)
    || CMP_3 H1Rn H2Rm ->
         CMP AL H1Rn (Dp_shift_immediate (LSL H2Rm) 0w)
    || MOV_3 H1Rd H2Rm ->
         MOV AL F H1Rd (Dp_shift_immediate (LSL H2Rm) 0w)
    || BX_ H2Rm ->
         BX AL H2Rm
    || LDR_3 Rd imm8 ->
         LDR AL F <| Pre := T; Up := T; Wb := F |> (w2w Rd) 15w
           (Dt_immediate (4w * w2w imm8))
    || STR_2  Rd Rn Rm ->
         STR AL F <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_shift_immediate (LSL (w2w Rm)) 0w)
    || STRH_2 Rd Rn Rm ->
         STRH AL <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dth_register (w2w Rm))
    || STRB_2 Rd Rn Rm ->
         STR AL T <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_shift_immediate (LSL (w2w Rm)) 0w)
    || LDRSB_ Rd Rn Rm ->
         LDRH AL T F <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dth_register (w2w Rm))
    || LDR_2  Rd Rn Rm ->
         LDR AL F <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_shift_immediate (LSL (w2w Rm)) 0w)
    || LDRH_2 Rd Rn Rm ->
         LDRH AL F T <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dth_register (w2w Rm))
    || LDRB_2 Rd Rn Rm ->
         LDR AL T <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_shift_immediate (LSL (w2w Rm)) 0w)
    || LDRSH_ Rd Rn Rm ->
         LDRH AL T T <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dth_register (w2w Rm))
    || STR_1  Rd Rn imm5 ->
         STR AL F <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_immediate (4w * w2w imm5))
    || LDR_1  Rd Rn imm5 ->
         LDR AL F <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_immediate (4w * w2w imm5))
    || STRB_1 Rd Rn imm5 ->
         STR AL T <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_immediate (w2w imm5))
    || LDRB_1 Rd Rn imm5 ->
         LDR AL T <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dt_immediate (w2w imm5))
    || STRH_1 Rd Rn imm5 ->
         STRH AL <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dth_immediate (2w * w2w imm5))
    || LDRH_1 Rd Rn imm5 ->
         LDRH AL F T <| Pre := T; Up := T; Wb := F |> (w2w Rd) (w2w Rn)
           (Dth_immediate (2w * w2w imm5))
    || STR_3 Rd imm8 ->
         STR AL F <| Pre := T; Up := T; Wb := F |> (w2w Rd) 13w
           (Dt_immediate (4w * w2w imm8))
    || LDR_4 Rd imm8 ->
         LDR AL F <| Pre := T; Up := T; Wb := F |> (w2w Rd) 13w
           (Dt_immediate (4w * w2w imm8))
    || ADD_5 Rd imm8 ->
         ADD AL F (w2w Rd) 15w (Dp_immediate 15w imm8)
    || ADD_6 Rd imm8 ->
         ADD AL F (w2w Rd) 13w (Dp_immediate 15w imm8)
    || ADD_7 imm7 ->
         ADD AL F 13w 13w (Dp_immediate 15w (w2w imm7))
    || SUB_4 imm7 ->
         SUB AL F 13w 13w (Dp_immediate 15w (w2w imm7))
    || PUSH R list ->
         STM AL F <| Pre := T; Up := F; Wb := T |> 13w
           (if R then 0x4000w !! w2w list else w2w list)
    || POP  R list ->
         LDM AL F <| Pre := F; Up := T; Wb := T |> 13w
           (if R then 0x8000w !! w2w list else w2w list)
    || STMIA_ Rn list ->
         STM AL F <| Pre := F; Up := T; Wb := T |> (w2w Rn) (w2w list)
    || LDMIA_ Rn list ->
         LDM AL F <| Pre := F; Up := T; Wb := ~(list ' (w2n Rn)) |>
           (w2w Rn) (w2w list)
    || B_1  cond imm8 ->
        (if cond = AL then
           UND AL
         else if cond = NV then
           SWI AL (w2w imm8)
         else
           B cond (sw2sw imm8))
    || UND_ ->
         UND AL
    || SWI_ imm8 ->
         SWI AL (w2w imm8)
    || B_2  imm11 ->
         B AL (sw2sw imm11)
    || BL_a imm11 ->
        (if imm11 = 0w then
           MOV AL F 14w (Dp_shift_immediate (LSL 15w) 0w)
         else
           BL AL (sw2sw imm11 << 11))
    || BL_b imm11 ->
         BL AL (w2w imm11))``;

(* ------------------------------------------------------------------------- *)

val word_index = METIS_PROVE [word_index_n2w]
  ``!i n. i < dimindex (:'a) ==> (((n2w n):'a word) ' i = BIT i n)``;

val word_index = REWRITE_RULE [BIT_def] word_index;

val extract_out_of_range = prove(
  `!w:'a word i h.
      (h - l < i) /\ i < dimindex(:'b) ==> ~((((h >< l) w):'b word) ' i)`,
  SRW_TAC [ARITH_ss,fcpLib.FCP_ss] [word_extract_def,word_bits_def,w2w]
\\ Cases_on `i < dimindex (:'a)` \\ SRW_TAC [ARITH_ss,fcpLib.FCP_ss] []);

val BIT_NUMERAL = CONJ (SPECL [`0`,`NUMERAL n`] BIT_def)
                       (SPECL [`NUMERAL b`,`NUMERAL n`] BIT_def);

val BITS_NUMERAL = (GEN_ALL o SPECL [`h`,`l`,`NUMERAL n`]) BITS_def;

val BITS_NUMERAL_ss = let open numeral_bitTheory numeralTheory in rewrites
  [BITS_NUMERAL, BITS_ZERO2, NUMERAL_DIV_2EXP, NUMERAL_iDIV2,
   NUMERAL_SFUNPOW_iDIV2, NUMERAL_SFUNPOW_iDUB, NUMERAL_SFUNPOW_FDUB,
   NUMERAL_BIT_MODIFY, NUMERAL_BIT_MODF, numeral_bitTheory.NUMERAL_BITWISE,
   numeral_bitTheory.iBITWISE, FDUB_iDIV2, FDUB_iDUB, FDUB_FDUB, iDUB_removal,
   numeral_suc, numeral_imod_2exp, MOD_2EXP, NORM_0]
end;

val condition_encode_AL = EVAL ``condition_encode AL``;

val thumb_to_arm = SIMP_RULE std_ss [pairTheory.pair_case_thm] THUMB_TO_ARM_def;

val thumb_encode = SIMP_RULE (std_ss++wordsLib.SIZES_ss++ARITH_ss)
  [word_lsl_def,word_or_def] thumb_encode_def;

val insts =
let val t = snd (dest_comb the_goal)
    val t = snd (dest_comb t)
in
  map fst (snd (TypeBase.strip_case t))
end;

val condition_encode__lem = prove(
  `!cond. ~(condition_encode_ cond ' 13)`,
  SRW_TAC [WORD_BIT_EQ_ss] [condition_encode__def]);

val dimindex_11 = EVAL ``dimindex(:11)``;

local
  fun THUMB_DECODE i n =
    (SIMP_CONV (srw_ss()++fcpLib.FCP_ss++wordsLib.SIZES_ss++BITS_NUMERAL_ss)
     [COND_RAND, COND_RATOR, thumb_encode,word_index,w2w,extract_out_of_range,
      condition_encode__lem, dimindex_11] o
     subst [``i:thumb_instruction`` |-> i, ``n:num`` |-> n]) ``(enc_ i) ' n``
in
  fun decode_thms nums insts =
     List.concat (map (fn i => map (THUMB_DECODE i) nums) insts);
end;
       
val thrms =
  (decode_thms [``15``,``14``,``13``,``12``,``11``,``10``,``9``,``8``] insts) @
  (decode_thms [``7``,``6``] (List.take(List.drop(insts, 11), 16))) @
  (decode_thms [``7``] (List.take(List.drop(insts, 50), 2))) @
  (decode_thms [``7``] [List.nth(insts, 30)]);

val extract_w2w_0 = prove(
  `!h l w:'a word. dimindex(:'a) <= l ==>
     ((h >< l) ((w2w w):'b word) = 0w:'c word)`,
  SRW_TAC [WORD_EXTRACT_ss] []);

val extract_w2w_w2w = prove(
  `!w:'a word. (h = dimindex(:'a) - 1) /\
          dimindex(:'a) <= dimindex(:'b) /\
          dimindex(:'a) <= dimindex(:'c) ==>
      ((h >< 0) ((w2w w):'b word) = w2w ((w2w w):'c word))`,
  SRW_TAC [ARITH_ss, WORD_EXTRACT_ss]
    [simpLib.SIMP_PROVE arith_ss [MIN_DEF]
       ``a <= b ==> (MIN a b = a) /\ (MIN b a = a)``]);

val extract_w2w_w2w_ = LIST_CONJ
  (map (fn a => (SIMP_RULE (std_ss++wordsLib.SIZES_ss)
         [dimindex_11,w2w_id] o INST_TYPE a) extract_w2w_w2w)
   [[`:'a` |-> `:3`, `:'b` |-> `:16`, `:'c` |-> `:4`],
    [`:'a` |-> `:5`, `:'b` |-> `:16`, `:'c` |-> `:32`, `:'d` |-> `:32`],
    [`:'a` |-> `:8`, `:'b` |-> `:16`, `:'c` |-> `:32`, `:'d` |-> `:32`],
    [`:'a` |-> `:11`, `:'b` |-> `:16`, `:'c` |-> `:24`, `:'d` |-> `:32`],
    [`:'a` |-> `:11`, `:'b` |-> `:16`, `:'c` |-> `:11`, `:'d` |-> `:11`]]);

val word_extract_n2w =
  SIMP_CONV std_ss [BITS_COMP_THM2, word_bits_n2w, word_extract_def, w2w_n2w]
  ``(h >< l) (n2w w)``;

val w2w_w2w_prove =
  simpLib.SIMP_PROVE (std_ss++wordsLib.SIZES_ss) [w2w_w2w, WORD_ALL_BITS];

val w2w_w2w_ = LIST_CONJ (map w2w_w2w_prove
  [``w2w (w2w (i:word3) : word8) : word32 = w2w (w2w i : word4)``,
   ``w2w (w2w (i:word5) : word12) : word32 = w2w i``,
   ``w2w (w2w (i:word7) : word8) : word32 = w2w i``,
   ``w2w (w2w (i:word8) : word16) : word32 = w2w i``,
   ``w2w (w2w (i:word8) : word24) : word32 = w2w i``]);

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val split_word4 = prove(
  `!w:word4. w2w w = (3 >< 3) w << 3 !! (2 >< 0) w : word32`,
  SRW_TAC [WORD_EXTRACT_ss] []);

val immediate8_times4 = prove(
  `!i:word8. w2w (4w:word12 * w2w i) = (w2w i << 2) : word32`,
  SRW_TAC [WORD_EXTRACT_ss, WORD_MUL_LSL_ss] []);

val immediate5_times4 = prove(
  `!i:word5. w2w (4w:word12 * w2w i) = (w2w i << 2) : word32`,
  SRW_TAC [WORD_EXTRACT_ss, WORD_MUL_LSL_ss] []);

val immediate5_times2 = prove(
  `(!i:word5. (7 >< 4) (2w:word8 * w2w i) = ((4 >< 3) i) : word32) /\
    !i:word5. (3 >< 0) (2w:word8 * w2w i) = ((2 >< 0) i << 1) : word32`,
  SRW_TAC [WORD_EXTRACT_ss, WORD_MUL_LSL_ss] []);

val w2n_lt8 = ((REWRITE_RULE [dimword_3] o INST_TYPE [`:'a` |-> `:3`]) w2n_lt);

val BLOCK_lem = prove(
  `!Rd:word3 imm:word8.
     (((w2w imm !! w2w Rd << 8) !! 51200w:word16) ' (w2n (w2w Rd : word32))) =
     (imm ' (w2n Rd))`,
  NTAC 2 STRIP_TAC  \\ Cases_on `imm`
    \\ RW_TAC (arith_ss++wordsLib.SIZES_ss) [w2n_w2w, w2w_n2w]
    \\ SPEC_THEN `Rd` ASSUME_TAC
         ((REWRITE_RULE [dimword_3] o INST_TYPE [`:'a` |-> `:3`]) w2n_lt)
    \\ `MIN 7 (w2n Rd) = w2n Rd` by SRW_TAC [ARITH_ss] [MIN_DEF]
    \\ `BITS (w2n Rd) (w2n Rd) 51200 = 0`
    by FULL_SIMP_TAC (std_ss++BITS_NUMERAL_ss) [LESS_THM]
    \\ SRW_TAC [fcpLib.FCP_ss,wordsLib.SIZES_ss,ARITH_ss]
         [BIT_def, BITS_COMP_THM2, n2w_def, word_lsl_def, w2w_def, word_or_def]
);

val BLOCK_lem2 = prove(
  `(!Rd:word3 imm:word8.
      (21 :+ T) ((w2w imm !! w2w Rd << 16) !! 3901751296w:word32) =
      (w2w imm !! w2w Rd << 16) !! 3903848448w) /\
   (!Rd:word3 imm:word8.
      (21 :+ T) ((w2w imm !! w2w Rd << 16) !! 3902799872w:word32) =
      (w2w imm !! w2w Rd << 16) !! 3902799872w) /\
    !Rd:word3 imm:word8.
      (21 :+ F) ((w2w imm !! w2w Rd << 16) !! 3901751296w:word32) =
      (w2w imm !! w2w Rd << 16) !! 3901751296w`,
  SRW_TAC [WORD_BIT_EQ_ss] []);

val COND_lem = prove(
  `(!c. (c = NV) = condition_encode_ c ' 11 /\ condition_encode_ c ' 10 /\
                   condition_encode_ c ' 9 /\ condition_encode_ c ' 8) /\
   (!c. (c = AL) = condition_encode_ c ' 11 /\ condition_encode_ c ' 10 /\
                   condition_encode_ c ' 9 /\ ~(condition_encode_ c ' 8))`,
  REPEAT STRIP_TAC \\ Cases_on `c` \\ EVAL_TAC \\ SRW_TAC [] []);

val COND_lem2 = prove(
  `!c. (case condition_encode_ c ' 11 of
        T -> (case condition_encode_ c ' 10 of
              T -> (case condition_encode_ c ' 9 of
                    T -> (case condition_encode_ c ' 8 of
                          T -> x || F -> y)
                 || F -> z)
           || F -> z)
     || F -> z) = if c = AL then y else if c = NV then x else z`,
  SRW_TAC [] [COND_lem] \\ FULL_SIMP_TAC (srw_ss()) [bool_case_ID]
    \\ FULL_SIMP_TAC std_ss []);

val COND_lem3 = prove(
  `(!c. (7 >< 0) (condition_encode_ c) = 0w :word8) /\
   (!c. (7 >< 0) (condition_encode_ c) = 0w :word32)`,
  REPEAT STRIP_TAC \\ Cases_on `c` \\ EVAL_TAC);

val COND_lem4 = prove(
  `!c. (11 >< 8) (condition_encode_ c) << 28 =  condition_encode c`,
  SRW_TAC [wordsLib.SIZES_ss, ARITH_ss]
    [condition_encode__def, condition_encode_def, WORD_EXTRACT_LSL, LSL_ADD,
     (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [w2w_id] o
      INST_TYPE [`:'a` |-> `:4`, `:'b` |-> `:16`,
                 `:'c` |-> `:32`, `:'d` |-> `:32`]) extract_w2w_w2w]);

val COND_lem5 = prove(
  `!c. (10 >< 0) (enc_ (BL_a c)) = c`,
  SRW_TAC [wordsLib.SIZES_ss, BITS_NUMERAL_ss]
     [thumb_encode_def, GSYM WORD_EXTRACT_OVER_BITWISE, word_extract_n2w,
      extract_w2w_w2w_, w2w_w2w, WORD_OR_CLAUSES]);

(* val _ = set_goal([], the_goal); *)

val thumb_to_arm_enc = Tactical.store_thm("thumb_to_arm_enc",
  the_goal,
  Cases_on `i` \\ SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC pure_ss ([COND_lem2, COND_lem5, COND_CLAUSES,
                          thumb_to_arm, bool_case_thm] @ thrms)
    \\ SRW_TAC [] []
    \\ SRW_TAC [boolSimps.LET_ss, wordsLib.SIZES_ss, BITS_NUMERAL_ss]
        [thumb_encode_def, instruction_encode_def, data_proc_encode_def,
         condition_encode_AL, shift_encode_def, addr_mode1_encode_def,
         addr_mode2_encode_def, addr_mode3_encode_def,
         options_encode_def, options_encode2_def,
         ZERO_SHIFT, SHIFT_ZERO, WORD_OR_CLAUSES, GSYM LSL_BITWISE, LSL_ADD,
         WORD_EXTRACT_COMP_THM, GSYM WORD_EXTRACT_OVER_BITWISE,
         GSYM WORD_w2w_OVER_BITWISE, WORD_EXTRACT_LSL, WORD_EXTRACT_ZERO, 
         WORD_EXTRACT_ZERO3, EXTRACT_ALL_BITS,
         word_extract_w2w, extract_w2w_0, extract_w2w_w2w_, w2w_id,
         word_lsl_n2w, word_or_n2w, word_modify_n2w, word_extract_n2w,
         w2w_n2w, w2w_0, w2w_w2w_, BLOCK_lem, BLOCK_lem2, COND_lem3, COND_lem4,
         immediate5_times4, immediate8_times4, immediate5_times2, split_word4]);

(* ------------------------------------------------------------------------- *)

val decode_27_enc_coproc_ = store_thm("decode_27_enc_coproc_",
  `(w2w (enc_ UND_): word32) ' 27 = F`, EVAL_TAC);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
