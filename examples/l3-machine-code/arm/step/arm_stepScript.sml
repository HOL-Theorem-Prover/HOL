(* ------------------------------------------------------------------------
   Definitions and theorems used by ARM step evaluator (arm_stepLib)
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib

open utilsLib
open wordsLib blastLib
open state_transformerTheory updateTheory alignmentTheory armTheory

val _ = new_theory "arm_step"
val _ = ParseExtras.temp_loose_equality()
(* ------------------------------------------------------------------------ *)

val _ = List.app (fn f => f ())
   [numLib.temp_prefer_num, wordsLib.prefer_word, wordsLib.guess_lengths]

(* ------------------------------------------------------------------------ *)

val NextStateARM_def = Define`
   NextStateARM s0 =
     let s1 = Next s0 in if s1.exception = NoException then SOME s1 else NONE`

val NextStateARM_arm = ustore_thm("NextStateARM_arm",
  `(s.exception = NoException) ==>
   (Fetch s = (ARM (v2w v), s with Encoding := Encoding_ARM)) /\
   (DecodeARM (v2w v) (s with Encoding := Encoding_ARM) =
       (ast, s with <| CurrentCondition := c;
                       Encoding := Encoding_ARM;
                       undefined := F |>)) /\
   (!s. Run ast s = f x s) /\
   (f x (s with <| CurrentCondition := c;
                   Encoding := Encoding_ARM;
                   undefined := F |>) = s1) /\
   (s1.Encoding = Encoding_ARM) /\
   (s1.exception = s.exception) ==>
   (NextStateARM s = SOME s1)`,
   lrw [NextStateARM_def, Next_def, Decode_def, ITAdvance_def]
   )

val NextStateARM_arm0 = ustore_thm("NextStateARM_arm0",
  `(s.exception = NoException) ==>
   (Fetch s = (ARM (v2w v), s with Encoding := Encoding_ARM)) /\
   (DecodeARM (v2w v) (s with Encoding := Encoding_ARM) =
       (ast, s with <| CurrentCondition := c;
                       Encoding := Encoding_ARM;
                       undefined := F |>)) /\
   (!s. Run ast s = f s) /\
   (f (s with <| CurrentCondition := c;
                 Encoding := Encoding_ARM;
                 undefined := F |>) = s1) /\
   (s1.Encoding = Encoding_ARM) /\
   (s1.exception = s.exception) ==>
   (NextStateARM s = SOME s1)`,
   lrw [NextStateARM_def, Next_def, Decode_def, ITAdvance_def]
   )

val NextStateARM_thumb = ustore_thm("NextStateARM_thumb",
  `(s.exception = NoException) ==>
   (Fetch s = (Thumb (v2w v), s with Encoding := Encoding_Thumb)) /\
   (DecodeThumb (v2w v) (s with Encoding := Encoding_Thumb) =
       (ast, s with <| CurrentCondition := c;
                       Encoding := Encoding_Thumb;
                       undefined := F |>)) /\
   (!s. Run ast s = f x s) /\
   (f x (s with <| CurrentCondition := c;
                   Encoding := Encoding_Thumb;
                   undefined := F |>) = s1) /\
   (ITAdvance () s1 = s2) /\
   (s2.exception = s.exception) ==>
   (NextStateARM s = SOME s2)`,
   lrw [NextStateARM_def, Next_def, Decode_def]
   )

(* ------------------------------------------------------------------------ *)

val LDM1_def = Define`
   LDM1 (f: word4 -> RName) b (registers: word16) s r j =
    (if word_bit j registers then
       f (n2w j) =+
       let a = b + if j = 0 then 0w else 4w * n2w (bit_count_upto j registers)
       in
          if s.CPSR.E then
             s.MEM a @@ s.MEM (a + 1w) @@ s.MEM (a + 2w) @@ s.MEM (a + 3w)
          else
             s.MEM (a + 3w) @@ s.MEM (a + 2w) @@ s.MEM (a + 1w) @@ s.MEM a
     else
        I) r`

val LDM_UPTO_def = Define`
   LDM_UPTO f i (registers: word16) (b: word32, s) =
     (b + 4w * n2w (bit_count_upto (i + 1) registers),
      s with REG := FOLDL (LDM1 f b registers s) s.REG (COUNT_LIST (i + 1)))`

val STM1_def = Define`
   STM1 f (b: word32) (registers: word16) s m j =
    (if word_bit j registers then
       let a = b + if j = 0 then 0w else 4w * n2w (bit_count_upto j registers)
       and r = s.REG (f (n2w j: word4))
       in
          (a + 3w =+ if s.CPSR.E then (7 >< 0) r else (31 >< 24) r) o
          (a + 2w =+ if s.CPSR.E then (15 >< 8) r else (23 >< 16) r) o
          (a + 1w =+ if s.CPSR.E then (23 >< 16) r else (15 >< 8) r) o
          (a =+ if s.CPSR.E then (31 >< 24) r else (7 >< 0) r)
     else
        I) m`

val STM_UPTO_def = Define`
   STM_UPTO f i (registers: word16) (b: word32, s) =
     (b + 4w * n2w (bit_count_upto (i + 1) registers),
      s with MEM := FOLDL (STM1 f b registers s) s.MEM (COUNT_LIST (i + 1)))`

(* ------------------------------------------------------------------------ *)

val DecodeRoundingMode_def = Define`
   DecodeRoundingMode (m: word2) =
     if m = 0w
        then roundTiesToEven
     else if m = 1w
        then roundTowardPositive
     else if m = 2w
        then roundTowardNegative
     else roundTowardZero`;

(* For floating-point single precision access *)

val SingleOfDouble_def = Define`
   SingleOfDouble b (w:word64) = if b then (63 >< 32) w else (31 >< 0) w`

val UpdateSingleOfDouble_def = Define`
   UpdateSingleOfDouble b (v:word32) (w:word64) =
      if b then
         bit_field_insert 63 32 v w
      else
         bit_field_insert 31 0 v w`;

(* ------------------------------------------------------------------------ *)

val reverse_endian_def = Define`
   reverse_endian (w: word32) =
   (7 >< 0) w @@ (15 >< 8) w @@ (23 >< 16) w @@ (31 >< 24) w`

(* ------------------------------------------------------------------------ *)

val GoodMode_def = Define`
   GoodMode (m: word5) = m IN {16w;17w;18w;19w;23w;27w;31w}`

val R_mode_def = Define`
   R_mode (m: word5) (n: word4) =
     case m, n of
       _,   0w  => RName_0usr
     | _,   1w  => RName_1usr
     | _,   2w  => RName_2usr
     | _,   3w  => RName_3usr
     | _,   4w  => RName_4usr
     | _,   5w  => RName_5usr
     | _,   6w  => RName_6usr
     | _,   7w  => RName_7usr
     | 17w, 8w  => RName_8fiq
     | _,   8w  => RName_8usr
     | 17w, 9w  => RName_9fiq
     | _,   9w  => RName_9usr
     | 17w, 10w => RName_10fiq
     | _,   10w => RName_10usr
     | 17w, 11w => RName_11fiq
     | _,   11w => RName_11usr
     | 17w, 12w => RName_12fiq
     | _,   12w => RName_12usr
     | 17w, 13w => RName_SPfiq
     | 18w, 13w => RName_SPirq
     | 19w, 13w => RName_SPsvc
     | 22w, 13w => RName_SPmon
     | 23w, 13w => RName_SPabt
     | 26w, 13w => RName_SPhyp
     | 27w, 13w => RName_SPund
     | _,   13w => RName_SPusr
     | 17w, 14w => RName_LRfiq
     | 18w, 14w => RName_LRirq
     | 19w, 14w => RName_LRsvc
     | 22w, 14w => RName_LRmon
     | 23w, 14w => RName_LRabt
     | 27w, 14w => RName_LRund
     | _,   14w => RName_LRusr
     | _        => RName_PC`

(* ------------------------------------------------------------------------ *)

val R_mode = Q.store_thm("R_mode",
   `(!m. R_mode m 0w = RName_0usr) /\
    (!m. R_mode m 1w = RName_1usr) /\
    (!m. R_mode m 2w = RName_2usr) /\
    (!m. R_mode m 3w = RName_3usr) /\
    (!m. R_mode m 4w = RName_4usr) /\
    (!m. R_mode m 5w = RName_5usr) /\
    (!m. R_mode m 6w = RName_6usr) /\
    (!m. R_mode m 7w = RName_7usr) /\
    (!m. R_mode m 15w = RName_PC)`,
   simp [R_mode_def]
   )

val R_x_not_pc = Q.prove(
   `!d mode. d <> 15w ==> (R_mode mode d <> RName_PC)`,
   wordsLib.Cases_word_value \\ simp [R_mode_def] \\ rw [])
   |> Drule.SPEC_ALL
   |> usave_as "R_x_not_pc"

val R_x_pc = Q.store_thm("R_x_pc",
   `!mode x. (R_mode mode x = RName_PC) = (x = 15w)`,
   REPEAT strip_tac
   \\ Cases_on `x = 15w`
   \\ asm_simp_tac (srw_ss()) [R_mode_def, DISCH_ALL R_x_not_pc]
   )

val BadMode = Q.prove(
   `!mode s. GoodMode mode ==> (BadMode mode s = F)`,
   rw [BadMode_def, GoodMode_def])
   |> Drule.SPEC_ALL
   |> usave_as "BadMode"

val NotMon = Q.prove(
   `!mode. GoodMode mode ==> mode <> 22w`,
   rw [GoodMode_def] \\ rw [])
   |> Drule.SPEC_ALL
   |> usave_as "NotMon"

val NotHyp = Q.prove(
   `!mode. GoodMode mode ==> mode <> 26w`,
   rw [GoodMode_def] \\ rw [])
   |> Drule.SPEC_ALL
   |> usave_as "NotHyp"

val R_mode_11 = Q.store_thm("R_mode_11",
   `!r1 r2 m. (R_mode m r1 = R_mode m r2) = (r1 = r2)`,
   wordsLib.Cases_word_value
   \\ simp [R_mode_def]
   \\ wordsLib.Cases_word_value
   \\ simp [R_mode_def]
   \\ rw []
   )

val IsSecure = Q.prove(
   `!s. ~s.Extensions Extension_Security ==> (IsSecure () s = T)`,
   rw [IsSecure_def, HaveSecurityExt_def, pred_setTheory.SPECIFICATION])
   |> Drule.SPEC_ALL
   |> usave_as "IsSecure"

val CurrentModeIsHyp = Q.prove(
   `!mode s. GoodMode s.CPSR.M ==> (CurrentModeIsHyp () s = (F, s))`,
   simp [CurrentModeIsHyp_def, DISCH_ALL BadMode, DISCH_ALL NotHyp])
   |> Drule.SPEC_ALL
   |> usave_as "CurrentModeIsHyp"

(* ------------------------------------------------------------------------ *)

val ITAdvance_0 = ustore_thm("ITAdvance_0",
   `(s.CPSR.IT = 0w) ==> (s with CPSR := s.CPSR with IT := 0w = s)`,
   lrw [armTheory.arm_state_component_equality,
        armTheory.PSR_component_equality]
   )

(* ------------------------------------------------------------------------ *)

val RoundingMode = Q.store_thm("RoundingMode",
   `!s. RoundingMode s = DecodeRoundingMode s.FP.FPSCR.RMode`,
   rw [DecodeRoundingMode_def, RoundingMode_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

(* ------------------------------------------------------------------------ *)

val notoverflow = METIS_PROVE [integer_wordTheory.overflow]
   ``!x y. (word_msb x = word_msb (x + y)) ==> (w2i (x + y) = w2i x + w2i y)``

val word_msb_sum1a = Q.prove(
   `!x y. (word_msb x = word_msb y) /\ word_msb (x + y) ==>
          word_msb (x + y + 1w)`,
   Cases \\ Cases
   \\ lrw [wordsTheory.word_msb_n2w_numeric, wordsTheory.word_add_n2w]
   \\ Cases_on `INT_MIN (:'a) <= n`
   \\ Cases_on `INT_MIN (:'a) <= n'`
   \\ lfs []
   >- (imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
       \\ pop_assum (K all_tac)
       \\ `p < INT_MIN (:'a) /\ p' < INT_MIN (:'a)`
       by lrw [wordsTheory.dimword_IS_TWICE_INT_MIN]
       \\ lfs [GSYM wordsTheory.dimword_IS_TWICE_INT_MIN]
       \\ `(p + (p' + (dimword (:'a) + 1)) = dimword (:'a) + (p + p' + 1)) /\
           (p + (p' + dimword (:'a)) = dimword (:'a) + (p + p'))` by lrw []
       \\ pop_assum SUBST_ALL_TAC \\ pop_assum SUBST1_TAC
       \\ full_simp_tac bool_ss
             [arithmeticTheory.ADD_MODULUS_RIGHT, wordsTheory.ZERO_LT_dimword]
       \\ `p + p' + 1 < dimword (:'a)`
       by lrw [wordsTheory.dimword_IS_TWICE_INT_MIN]
       \\ lfs [])
   \\ fs [arithmeticTheory.NOT_LESS_EQUAL]
   \\ `n + n' + 1 < dimword (:'a)`
   by lrw [wordsTheory.dimword_IS_TWICE_INT_MIN]
   \\ lfs []
   )

val word_msb_sum1b = Q.prove(
   `!x y. (word_msb x <> word_msb y) /\ ~word_msb (x + y) ==>
          (word_msb (x + y) = word_msb (x + y + 1w))`,
   Cases \\ Cases
   \\ simp_tac std_ss
         [wordsTheory.word_msb_n2w_numeric, wordsTheory.word_add_n2w]
   \\ lrw []
   \\ Cases_on `n < INT_MIN (:'a)`
   \\ Cases_on `n' < INT_MIN (:'a)`
   \\ lfs [arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_LESS_EQUAL]
   \\ Cases_on `n + (n' + 1) < dimword (:'a)`
   \\ lfs [arithmeticTheory.NOT_LESS]
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ pop_assum (K all_tac)
   \\ `p < INT_MIN (:'a)` by lfs [wordsTheory.dimword_IS_TWICE_INT_MIN]
   \\ lrw [arithmeticTheory.ADD_MODULUS_LEFT]
   )

val word_msb_sum1c = Q.prove(
   `!x y. word_msb (x + y + 1w) /\ ~word_msb (x + y) ==> (x + y = INT_MAXw)`,
   Cases \\ Cases
   \\ `INT_MIN (:'a) - 1 < dimword (:'a)`
   by (assume_tac wordsTheory.INT_MIN_LT_DIMWORD \\ decide_tac)
   \\ simp_tac std_ss
        [wordsTheory.word_msb_n2w_numeric, wordsTheory.word_H_def,
         wordsTheory.INT_MAX_def, wordsTheory.word_add_n2w]
   \\ lrw []
   \\ lfs [arithmeticTheory.NOT_LESS_EQUAL]
   \\ Cases_on `n + (n' + 1) < dimword (:'a)`
   \\ lfs [arithmeticTheory.NOT_LESS]
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ pop_assum (K all_tac)
   \\ `p < dimword (:'a)` by lfs []
   \\ Cases_on `n + n' < dimword (:'a)`
   \\ lfs [arithmeticTheory.ADD_MODULUS_LEFT, arithmeticTheory.NOT_LESS]
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ pop_assum (K all_tac)
   \\ lfs [arithmeticTheory.ADD_MODULUS_LEFT]
   )

val AddWithCarry = Q.store_thm("AddWithCarry",
   `!x y carry_in. AddWithCarry (x,y,carry_in) = add_with_carry (x,y,carry_in)`,
   REPEAT strip_tac
   \\ simp [AddWithCarry_def, wordsTheory.add_with_carry_def]
   \\ simp [GSYM wordsTheory.word_add_n2w]
   \\ Cases_on `carry_in`
   \\ simp [integer_wordTheory.overflow]
   \\ Cases_on `dimindex(:'a) = 1`
   >- (imp_res_tac wordsTheory.dimindex_1_cases
       \\ pop_assum (fn th => (strip_assume_tac (Q.SPEC `x` th)
                            \\ strip_assume_tac (Q.SPEC `y` th)))
       \\ simp [wordsTheory.word_index, wordsTheory.word_msb_def,
                wordsTheory.word_2comp_def, integer_wordTheory.w2i_def,
                wordsTheory.dimword_def])
   \\ Cases_on `word_msb (x + y) <> word_msb (1w : 'a word)`
   \\ `~word_msb 1w`
   by lrw [wordsTheory.word_msb_n2w, DECIDE ``0n < n /\ n <> 1 ==> ~(n <= 1)``]
   \\ fs [integer_wordTheory.different_sign_then_no_overflow,
          integer_wordTheory.overflow, integer_wordTheory.w2i_1]
   >- (Cases_on `word_msb x <=> word_msb y` \\ simp [word_msb_sum1a])
   \\ Cases_on `word_msb x = word_msb y`
   \\ simp [GSYM integer_wordTheory.different_sign_then_no_overflow]
   >- (Cases_on `word_msb (x + y + 1w)`
       \\ lfs [notoverflow, integer_wordTheory.w2i_1]
       >- (imp_res_tac word_msb_sum1c
           \\ lfs [integer_wordTheory.w2i_INT_MINw]
           \\ Cases_on `x`
           \\ Cases_on `y`
           \\ lfs [wordsTheory.word_msb_n2w_numeric]
           \\ Cases_on `INT_MIN (:'a) <= n'`
           \\ lfs [integer_wordTheory.w2i_n2w_pos,
                   integer_wordTheory.w2i_n2w_neg,
                   wordsTheory.word_add_n2w,
                   wordsTheory.word_L_def,
                   wordsTheory.word_2comp_def,
                   integerTheory.INT_ADD_CALCULATE]
           \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
           \\ `p + p' < dimword (:'a)`
           by lfs [wordsTheory.dimword_IS_TWICE_INT_MIN]
           \\ lfs [GSYM wordsTheory.dimword_IS_TWICE_INT_MIN]
           \\ `(p + (p' + dimword (:'a)) = (p + p') + dimword (:'a)) /\
               (INT_MIN (:'a) + dimword (:'a) - 1 =
                dimword (:'a) + (INT_MIN (:'a) - 1))`
           by lfs []
           \\ ntac 2 (pop_assum SUBST_ALL_TAC)
           \\ full_simp_tac bool_ss
                 [arithmeticTheory.ADD_MODULUS_LEFT,
                  arithmeticTheory.ADD_MODULUS_RIGHT,
                  wordsTheory.ZERO_LT_dimword]
           \\ lfs [wordsTheory.BOUND_ORDER]
           \\ metis_tac [arithmeticTheory.ADD_ASSOC,
                         wordsTheory.dimword_sub_int_min,
                         wordsTheory.ZERO_LT_INT_MIN,
                         DECIDE ``0n < n ==> (n - 1 + 1 = n)``])
       \\ metis_tac [integer_wordTheory.overflow, integer_wordTheory.w2i_1])
   \\ `word_msb (x + y) <=> word_msb (x + y + 1w)` by imp_res_tac word_msb_sum1b
   \\ simp [notoverflow, integer_wordTheory.w2i_1]
   )

(* ------------------------------------------------------------------------ *)

val CountLeadingZeroBits16 = Q.store_thm("CountLeadingZeroBits16",
   `!w:word16.
       CountLeadingZeroBits w = if w = 0w then 16 else 15 - w2n (word_log2 w)`,
   lrw [CountLeadingZeroBits_def, HighestSetBit_def]
   \\ `LOG2 (w2n w) < 16`
   by metis_tac [wordsTheory.LOG2_w2n_lt, EVAL ``dimindex(:16)``]
   \\ lrw [integer_wordTheory.w2i_def, wordsTheory.word_log2_def,
           wordsTheory.word_msb_n2w_numeric,
           intLib.ARITH_PROVE ``j < 16 ==> (Num (15 - &j) = 15 - j)``]
   )

val CountLeadingZeroBits32 = Q.store_thm("CountLeadingZeroBits32",
   `!w:word32.
       CountLeadingZeroBits w = if w = 0w then 32 else 31 - w2n (word_log2 w)`,
   lrw [CountLeadingZeroBits_def, HighestSetBit_def]
   \\ `LOG2 (w2n w) < 32`
   by metis_tac [wordsTheory.LOG2_w2n_lt, EVAL ``dimindex(:32)``]
   \\ lrw [integer_wordTheory.w2i_def, wordsTheory.word_log2_def,
           wordsTheory.word_msb_n2w_numeric,
           intLib.ARITH_PROVE ``j < 32 ==> (Num (31 - &j) = 31 - j)``]
   )

val FOLDL_AUG = Q.prove(
   `!f a l.
      FOLDL (\x i. f x i) a l =
      FST (FOLDL (\y i. (f (FST y) i, ())) (a, ()) l)`,
   Induct_on `l` \\ lrw []
   )

val FOLDL_cong = Q.store_thm("FOLDL_cong",
   `!l r f g a b.
      (LENGTH l = LENGTH r) /\ (a = b) /\
      (!i x. i < LENGTH l ==> (f x (EL i l) = g x (EL i r))) ==>
      (FOLDL f a l = FOLDL g b r)`,
   Induct \\ lrw []
   \\ Cases_on `r` \\ lfs []
   \\ metis_tac [prim_recTheory.LESS_0, listTheory.EL, listTheory.HD,
                 listTheory.EL_restricted, arithmeticTheory.LESS_MONO_EQ]
   )

val FOR_BASE = Q.store_thm("FOR_BASE",
   `!f s. FOR (n, n, f) s = f n s`,
   simp [Once state_transformerTheory.FOR_def])

val FOR_FOLDL = Q.store_thm("FOR_FOLDL",
   `!i j f s.
       i <= j ==>
       (FOR (i, j, f) s =
        ((), FOLDL (\x n. SND (f (n + i) x)) s (COUNT_LIST (j - i + 1))))`,
   ntac 2 strip_tac \\ Induct_on `j - i`
   \\ lrw [Once state_transformerTheory.FOR_def, pairTheory.UNCURRY,
           state_transformerTheory.BIND_DEF]
   >- (`i = j` by decide_tac
       \\ simp []
       \\ EVAL_TAC
       \\ Cases_on `f j s`
       \\ simp [oneTheory.one])
   \\ `v = j - (i + 1)` by decide_tac
   \\ qpat_assum `!j i. P` (qspecl_then [`j`, `i + 1`] imp_res_tac)
   \\ Cases_on `i + 1 < j`
   >- (`j + 1 - i = SUC (j - i)` by decide_tac
       \\ lrw [rich_listTheory.COUNT_LIST_def]
       \\ match_mp_tac FOLDL_cong
       \\ lrw [rich_listTheory.COUNT_LIST_GENLIST, listTheory.MAP_GENLIST,
               arithmeticTheory.ADD1])
   \\ `j = i + 1` by decide_tac
   \\ simp []
   \\ EVAL_TAC
   )

val BitCount = Q.store_thm("BitCount",
   `!w. BitCount w = bit_count w`,
   lrw [BitCount_def, wordsTheory.bit_count_def, wordsTheory.bit_count_upto_def,
        wordsTheory.word_bit_def]
   \\ `0 <= dimindex(:'a) - 1` by lrw []
   \\ simp
       [FOR_FOLDL
        |> Q.ISPECL [`0n`, `dimindex(:'a) - 1`,
                     `\i state: num # unit.
                         ((),
                          if i <= dimindex(:'a) - 1 /\ w ' i then
                             (FST state + 1, ())
                          else
                             state)`],
        sum_numTheory.SUM_FOLDL]
   \\ REWRITE_TAC
        [FOLDL_AUG
         |> Q.ISPECL
              [`\x:num i. x + if w ' i then 1 else 0`, `0`,
               `COUNT_LIST (dimindex ((:'a) :'a itself))`]
         |> SIMP_RULE (srw_ss())[]]
   \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (FST x = FST y)``)
   \\ MATCH_MP_TAC listTheory.FOLDL_CONG
   \\ lrw [rich_listTheory.MEM_COUNT_LIST,
           DECIDE ``0n < n ==> (n - 1 + 1 = n)``]
   \\ Cases_on `a`
   \\ simp []
   )

val bit_count_upto_1 = Q.prove(
   `!registers: word16.
       4w * n2w (bit_count_upto 1 registers) =
       if word_bit 0 registers then 4w else 0w: word32`,
   EVAL_TAC \\ lrw [wordsTheory.word_bit_def]
   )

val bit_count_sub = Q.prove(
   `!r: 'a word.
      n2w (bit_count_upto (dimindex(:'a) - 1) r) - n2w (bit_count r) =
      if r ' (dimindex(:'a) - 1) then -1w else 0w`,
   REPEAT strip_tac
   \\ simp [wordsTheory.bit_count_def]
   \\ Cases_on `dimindex(:'a)`
   >- lfs [DECIDE ``0 < n ==> (n <> 0n)``]
   \\ simp [arithmeticTheory.SUC_SUB1, GSYM wordsTheory.word_add_n2w,
            wordsTheory.WORD_LEFT_ADD_DISTRIB, wordsTheory.bit_count_upto_SUC]
   \\ rw [])
   |> Thm.INST_TYPE [Type.alpha |-> ``:16``]
   |> SIMP_RULE (std_ss++wordsLib.SIZES_ss) []
   |> Conv.CONV_RULE (Conv.DEPTH_CONV (wordsLib.WORD_BIT_INDEX_CONV false))
   |> save_as "bit_count_sub"

val bit_count_lt_1 = Q.store_thm("bit_count_lt_1",
   `!w. bit_count w < 1 = (w = 0w)`,
   rewrite_tac [DECIDE ``a < 1n = (a = 0)``, wordsTheory.bit_count_is_zero]
   )

(* ------------------------------------------------------------------------ *)

val Align = Q.store_thm("Align",
   `(!w. Align (w, 1) = align 0 w) /\
    (!w. Align (w, 2) = align 1 w) /\
    (!w. Align (w, 4) = align 2 w) /\
    (!w. Align (w, 8) = align 3 w) /\
    (!w. Align (w, 16) = align 4 w)`,
    simp [armTheory.Align_def, alignmentTheory.align_w2n]
    )

val Aligned = Q.store_thm("Aligned",
   `(!w. Aligned (w, 1) = aligned 0 w) /\
    (!w. Aligned (w, 2) = aligned 1 w) /\
    (!w. Aligned (w, 4) = aligned 2 w) /\
    (!w. Aligned (w, 8) = aligned 3 w) /\
    (!w. Aligned (w, 16) = aligned 4 w)`,
    simp [armTheory.Aligned_def, Align, alignmentTheory.aligned_def,
          boolTheory.EQ_SYM_EQ]
    )

val aligned_23 = Q.store_thm("aligned_23",
   `(!w: word32. ((1 >< 0) w = 0w: word2) = aligned 2 w) /\
    (!w: word32. ((2 >< 0) w = 0w: word3) = aligned 3 w)`,
    simp [alignmentTheory.aligned_extract]
    \\ blastLib.BBLAST_TAC
   )

val AlignedAlign = ustore_thm("AlignedAlign",
   `aligned p v ==> ((if b then align p v else v) = v)`,
   lrw [alignmentTheory.aligned_def, alignmentTheory.align_align]
   )

val Aligned_concat4 = Q.store_thm("Aligned_concat4",
   `!p a: word8 b: word8 c: word8 d: word8.
      aligned 2 (if p then a @@ b @@ c @@ d else d @@ c @@ b @@ a) =
      aligned 2 (if p then d else a)`,
   lrw [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val Aligned4_bit0_t = utilsLib.ustore_thm ("Aligned4_bit0_t",
   `aligned 2 (pc: word32) ==> ~word_bit 0 (pc + 4w)`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val Aligned4_bit1_t = utilsLib.ustore_thm ("Aligned4_bit1_t",
   `aligned 2 (pc: word32) ==> ~word_bit 1 (pc + 4w)`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val Aligned4_bit0 = utilsLib.ustore_thm ("Aligned4_bit0",
   `aligned 2 (pc: word32) ==> ~word_bit 0 (pc + 8w)`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val Aligned4_bit1 = utilsLib.ustore_thm ("Aligned4_bit1",
   `aligned 2 (pc: word32) ==> ~word_bit 1 (pc + 8w)`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val Aligned_BranchTarget_thumb =
   utilsLib.ustore_thm("Aligned_BranchTarget_thumb",
   `aligned 1 (pc: word32) ==>
    (aligned 1 (pc + (if b then 4w else 8w) + imm32) = aligned 1 imm32)`,
   Cases_on `b`
   \\ simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val Aligned_BranchTarget_arm = utilsLib.ustore_thm("Aligned_BranchTarget_arm",
   `aligned 2 (pc: word32) ==>
    (aligned 2 (pc + (if b then 4w else 8w) + imm32) = aligned 2 imm32)`,
   Cases_on `b`
   \\ simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val Aligned_Align_plus_minus = Q.store_thm("Aligned_Align_plus_minus",
   `(!w x: word32. aligned 2 (align 2 w + x) = aligned 2 x) /\
    (!w x: word32. aligned 2 (align 2 w - x) = aligned 2 x) /\
    (!w x: word32. aligned 1 (align 2 w + x) = aligned 1 x) /\
    (!w x: word32. aligned 1 (align 2 w - x) = aligned 1 x)`,
   lrw [alignmentTheory.aligned_extract, alignmentTheory.align_def]
   \\ blastLib.BBLAST_TAC
   )

val AlignedPC_plus_thumb = utilsLib.ustore_thm("AlignedPC_plus_thumb",
   `aligned 1 (w: word32) ==> (align 1 (w + 4w + v) = w + align 1 v + 4w)`,
   simp [alignmentTheory.aligned_extract, alignmentTheory.align_def]
   \\ blastLib.BBLAST_TAC
   )

val AlignedPC_plus_xthumb = utilsLib.ustore_thm("AlignedPC_plus_xthumb",
   `aligned 1 (w: word32) ==>
    (((31 >< 1) (w + 4w): 31 word) @@ (1w: word1) = w + 5w)`,
   simp [alignmentTheory.aligned_extract] \\ blastLib.BBLAST_TAC
   )

val AlignedPC_plus_align_arm = utilsLib.ustore_thm("AlignedPC_plus_align_arm",
   `aligned 2 (w: word32) ==>
    (align 2 (align 2 (w + 8w) + v) = w + align 2 v + 8w)`,
   simp [alignmentTheory.aligned_extract, alignmentTheory.align_def]
   \\ blastLib.BBLAST_TAC
   )

val AlignedPC_plus_xarm = utilsLib.ustore_thm("AlignedPC_plus_xarm",
   `aligned 2 (w: word32) ==> (align 1 (w + 8w + v) = w + align 1 v + 8w)`,
   simp [alignmentTheory.aligned_extract, alignmentTheory.align_def]
   \\ blastLib.BBLAST_TAC
   )

val Aligned_plus_minus = utilsLib.ustore_thm("Aligned_plus_minus",
   `aligned 2 (x: word32) ==>
    (aligned 2 (if a then x + y else x - y) = aligned 2 y)`,
   lrw [alignmentTheory.aligned_extract] \\ blastLib.FULL_BBLAST_TAC
   )

val Aligned4_base_pc_plus = utilsLib.ustore_thm("Aligned4_base_pc_plus",
   `aligned (if t then 1 else 2) (pc: word32) ==>
    (aligned 2 (pc + (if t then 4w else 8w) + x) =
     if t then aligned 2 (pc + x) else aligned 2 x)`,
   lrw [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC
   )

val Aligned4_base_pc_minus = utilsLib.ustore_thm("Aligned4_base_pc_minus",
   `aligned (if t then 1 else 2) (pc: word32) ==>
    (aligned 2 (pc + (if t then 4w else 8w) - x) =
     if t then aligned 2 (pc - x) else aligned 2 x)`,
   lrw [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC
   )

val Aligned2_base_pc_plus = utilsLib.ustore_thm("Aligned2_base_pc_plus",
   `aligned (if t then 1 else 2) (pc: word32) ==>
    (aligned 1 (pc + (if t then 4w else 8w) + x) = aligned 1 x)`,
   lrw [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC
   )

val Aligned2_base_pc_minus = utilsLib.ustore_thm("Aligned2_base_pc_minus",
   `aligned (if t then 1 else 2) (pc: word32) ==>
    (aligned 1 (pc + (if t then 4w else 8w) - x) = aligned 1 x)`,
   lrw [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC
   )

val Align4_base_pc_plus = utilsLib.ustore_thm("Align4_base_pc_plus",
   `aligned (if t then 1 else 2) (pc: word32) ==>
    (align 2 (pc + if t then 4w else 8w) + x =
     if t then align 2 pc + (x + 4w) else pc + (x + 8w))`,
   lrw [alignmentTheory.aligned_extract, alignmentTheory.align_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

val Align4_base_pc_minus = utilsLib.ustore_thm("Align4_base_pc_minus",
   `aligned (if t then 1 else 2) (pc: word32) ==>
    (align 2 (pc + if t then 4w else 8w) - x =
     if t then align 2 pc - (x - 4w) else pc - (x - 8w))`,
   lrw [alignmentTheory.aligned_extract, alignmentTheory.align_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

(* ------------------------------------------------------------------------ *)

val Align_branch_immediate = Q.store_thm("Align_branch_immediate",
   `a +
    align 2
      (sw2sw ((v2w [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11;
                    x12; x13; x14; x15; x16; x17; x18; x19; x20; x21;
                    x22; x23]: word24 @@ (0w: word2)): 26 word): word32) =
    if x0 then
       a -
       (v2w [~x1; ~x2; ~x3; ~x4; ~x5; ~x6; ~x7; ~x8; ~x9; ~x10; ~x11; ~x12;
             ~x13; ~x14; ~x15; ~x16; ~x17; ~x18; ~x19; ~x20; ~x21; ~x22; ~x23;
             T; T] + 1w)
    else
       a +
       v2w [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15;
            x16; x17; x18; x19; x20; x21; x22; x23; F; F]`,
   lrw [alignmentTheory.align_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

val Align_branch_exchange_immediate =
   Q.store_thm("Align_branch_exchange_immediate",
   `a +
    align 1
      (sw2sw ((v2w [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11;
                    x12; x13; x14; x15; x16; x17; x18; x19; x20; x21;
                    x22; x23]: word24 @@
               (v2w [x24; F]: word2)): 26 word): word32) =
    if x0 then
       a -
       (v2w [~x1; ~x2; ~x3; ~x4; ~x5; ~x6; ~x7; ~x8; ~x9; ~x10; ~x11; ~x12;
             ~x13; ~x14; ~x15; ~x16; ~x17; ~x18; ~x19; ~x20; ~x21; ~x22; ~x23;
             ~x24; T] + 1w)
    else
       a +
       v2w [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15;
            x16; x17; x18; x19; x20; x21; x22; x23; x24; F]`,
   lrw [alignmentTheory.align_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

local
   val t2 = ``(((31 >< 1) (i: word32) : 31 word) @@ (0w: word1)): word32``
   val lem = Q.prove(
      `(!i:word32. ^t2 = align 1 i) /\
       (!i:word32. ((31 >< 2) i : 30 word) @@ (0w: word2) = align 2 i)`,
      simp [alignmentTheory.align_def]
      \\ blastLib.BBLAST_TAC
      )
   val lem2 = Q.prove(
      `(!i: word32.  (if word_bit 0 i then ^t2 else i) = align 1 i)`,
      lrw [lem, alignmentTheory.align_def]
      \\ blastLib.FULL_BBLAST_TAC
      )
in
   val Align_LoadWritePC = Theory.save_thm("Align_LoadWritePC",
      Thm.CONJ lem2 lem)
end

(* ------------------------------------------------------------------------ *)

val take_id_imp =
   metisLib.METIS_PROVE [listTheory.TAKE_LENGTH_ID]
     ``!n w:'a list. (n = LENGTH w) ==> (TAKE n w = w)``

fun concat_tac l =
  ntac (List.length l) strip_tac
  \\ map_every bitstringLib.Cases_on_v2w l
  \\ lfs [markerTheory.Abbrev_def]
  \\ REPEAT (once_rewrite_tac [bitstringTheory.word_concat_v2w_rwt]
             \\ simp [bitstringTheory.w2v_v2w, bitstringTheory.fixwidth_id_imp])

fun extract_bytes_tac l =
  lrw []
  \\ map_every bitstringLib.Cases_on_v2w l
  \\ lfs [markerTheory.Abbrev_def]
  \\ ntac (List.length l - 1)
       (once_rewrite_tac [bitstringTheory.word_concat_v2w_rwt]
        \\ simp [bitstringTheory.w2v_v2w, bitstringTheory.fixwidth_id_imp])
  \\ lrw [bitstringTheory.field_def, bitstringTheory.shiftr_def,
          listTheory.TAKE_APPEND1, take_id_imp, bitstringTheory.fixwidth_id_imp]
  \\ lrw [bitstringTheory.fixwidth_def, rich_listTheory.DROP_APPEND2]

val concat16 = Q.store_thm("concat16",
   `!w1:word8 w2:word8. w2v w1 ++ w2v w2 = w2v (w1 @@ w2)`,
   concat_tac [`w1`,`w2`]
   )

val concat32 = Q.store_thm("concat32",
   `!w1:word8 w2:word8 w3:word16.
      w2v w1 ++ (w2v w2 ++ w2v w3) = w2v (w1 @@ w2 @@ w3)`,
   concat_tac [`w1`,`w2`,`w3`]
   )

val concat64 = Q.store_thm("concat64",
   `!w1:word8 w2:word8 w3:word8 w4:word8 w5:word32.
      w2v w1 ++ (w2v w2 ++ (w2v w3 ++ (w2v w4 ++ w2v w5))) =
      w2v (w1 @@ w2 @@ w3 @@ w4 @@ w5)`,
   concat_tac [`w1`,`w2`,`w3`,`w4`,`w5`]
   )

val extract16 = Q.store_thm("extract16",
   `!w1:word8 w2:word8.
      field 7 0 (w2v (w1 @@ w2)) ++ field 15 8 (w2v (w1 @@ w2)) =
      w2v (w2 @@ w1)`,
   extract_bytes_tac [`w1`, `w2`]
   )

val extract32 = Q.prove(
   `!w1:word8 w2:word8 w3:word8 w4:word8.
       let r = w1 @@ w2 @@ w3 @@ w4 in
       field 7 0 (w2v r) ++ (field 15 8 (w2v r) ++
       (field 23 16 (w2v r) ++ (field 31 24 (w2v r)))) =
       w2v (w4 @@ w3 @@ w2 @@ w1)`,
   extract_bytes_tac [`w1`, `w2`, `w3`, `w4`])
   |> SIMP_RULE (bool_ss++boolSimps.LET_ss) []
   |> save_as "extract32"

val extract64 = Q.prove(
   `!w1:word8 w2:word8 w3:word8 w4:word8
     w5:word8 w6:word8 w7:word8 w8:word8.
       let r = w1 @@ w2 @@ w3 @@ w4 @@ w5 @@ w6 @@ w7 @@ w8 in
       field 7 0 (w2v r) ++ (field 15 8 (w2v r) ++
       (field 23 16 (w2v r) ++ (field 31 24 (w2v r) ++
       (field 39 32 (w2v r) ++ (field 47 40 (w2v r) ++
       (field 55 48 (w2v r) ++ (field 63 56 (w2v r)))))))) =
       w2v (w8 @@ w7 @@ w6 @@ w5 @@ w4 @@ w3 @@ w2 @@ w1)`,
   extract_bytes_tac [`w1`, `w2`, `w3`, `w4`,`w5`, `w6`, `w7`, `w8`])
   |> SIMP_RULE (bool_ss++boolSimps.LET_ss) []
   |> save_as "extract64"

val concat_bytes = Q.store_thm("concat_bytes",
   `!w: word32. (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w`,
   blastLib.BBLAST_TAC
   )

val reverse_endian_bytes = Q.store_thm("reverse_endian_bytes",
   `!w: word32.
       ((7 >< 0) (reverse_endian w) = (31 >< 24) w) /\
       ((15 >< 8) (reverse_endian w) = (23 >< 16) w) /\
       ((23 >< 16) (reverse_endian w) = (15 >< 8) w) /\
       ((31 >< 24) (reverse_endian w) = (7 >< 0) w)`,
   rw [reverse_endian_def]
   \\ blastLib.BBLAST_TAC
   )

val reverse_endian_id = Q.store_thm("reverse_endian_id",
   `!w. reverse_endian (reverse_endian w) = w`,
   rw [reverse_endian_def, reverse_endian_bytes, concat_bytes]
   )

(* ------------------------------------------------------------------------ *)

fun field_thm a b h l =
   bitstringTheory.extract_v2w
   |> Thm.INST_TYPE
         [Type.alpha |-> fcpSyntax.mk_int_numeric_type a,
          Type.beta  |-> fcpSyntax.mk_int_numeric_type b]
   |> Q.SPECL [h, l]
   |> SIMP_RULE (srw_ss()) []
   |> Conv.GSYM

val field16 = Q.store_thm("field16",
   `(!w: word16.
       v2w (field 15 8 (field 7 0 (w2v w) ++ field 15 8 (w2v w))) =
       (7 >< 0) w : word8) /\
    (!w: word16. v2w (field 15 8 (w2v w)) = (15 >< 8) w : word8) /\
    (!w: word16.
       v2w (field 7 0 (field 7 0 (w2v w) ++ field 15 8 (w2v w))) =
       (15 >< 8) w : word8) /\
    (!w: word16. v2w (field 7 0 (w2v w)) = (7 >< 0) w : word8)`,
    lrw [bitstringTheory.field_concat_left, bitstringTheory.field_concat_right,
         bitstringTheory.field_id_imp]
    \\ simp [field_thm 16 8 `7` `0`, field_thm 16 8 `15` `8`]
    \\ srw_tac [wordsLib.WORD_EXTRACT_ss] []
    )

val field32 = Q.store_thm("field32",
   `(!w: word32.
       v2w (field 31 24
              (field 7 0 (w2v w) ++ (field 15 8 (w2v w) ++
              (field 23 16 (w2v w) ++ field 31 24 (w2v w))))) =
       (7 >< 0) w : word8) /\
    (!w: word32. v2w (field 31 24 (w2v w)) = (31 >< 24) w : word8) /\
    (!w: word32.
       v2w (field 23 16
              (field 7 0 (w2v w) ++ (field 15 8 (w2v w) ++
              (field 23 16 (w2v w) ++ field 31 24 (w2v w))))) =
       (15 >< 8) w : word8) /\
    (!w: word32. v2w (field 23 16 (w2v w)) = (23 >< 16) w : word8) /\
    (!w: word32.
       v2w (field 15 8
              (field 7 0 (w2v w) ++ (field 15 8 (w2v w) ++
              (field 23 16 (w2v w) ++ field 31 24 (w2v w))))) =
       (23 >< 16) w : word8) /\
    (!w: word32. v2w (field 15 8 (w2v w)) = (15 >< 8) w : word8) /\
    (!w: word32.
       v2w (field 7 0
              (field 7 0 (w2v w) ++ (field 15 8 (w2v w) ++
              (field 23 16 (w2v w) ++ field 31 24 (w2v w))))) =
       (31 >< 24) w : word8) /\
    (!w: word32. v2w (field 7 0 (w2v w)) = (7 >< 0) w : word8)`,
    lrw [bitstringTheory.field_concat_left, bitstringTheory.field_concat_right,
         bitstringTheory.field_id_imp]
    \\ simp [field_thm 32 8 `7` `0`, field_thm 32 8 `15` `8`,
             field_thm 32 8 `23` `16`, field_thm 32 8 `31` `24`]
    \\ srw_tac [wordsLib.WORD_EXTRACT_ss] []
    )

val fixwidth_w2v = Q.prove(
  `!w : 'a word. fixwidth (dimindex (:'a)) (w2v w) = w2v w`,
  simp [])

val field_insert = Q.store_thm("field_insert",
  `!msb lsb a : word32 b : word32.
     v2w (field_insert msb lsb (field (msb - lsb) 0 (w2v a)) (w2v b)) : word32 =
     bit_field_insert msb lsb a b`,
  simp [bitstringTheory.field_insert_def, wordsTheory.bit_field_insert_def]
  \\ once_rewrite_tac [GSYM fixwidth_w2v]
  \\ simp_tac (bool_ss++fcpLib.FCP_ss)
       [GSYM bitstringTheory.word_modify_v2w, bitstringTheory.v2w_w2v,
        wordsTheory.WORD_MODIFY_BIT]
  \\ simp [fixwidth_w2v]
  \\ rw []
  \\ `(?p. p + lsb = i)` by metis_tac [arithmeticTheory.LESS_EQ_ADD_EXISTS]
  \\ pop_assum (SUBST_ALL_TAC o GSYM)
  \\ fs []
  \\ `?q. q + (lsb + p) = msb`
  by metis_tac [arithmeticTheory.LESS_EQ_ADD_EXISTS]
  \\ pop_assum (SUBST_ALL_TAC o GSYM)
  \\ `SUC (p + q) - (q + 1) = p` by decide_tac
  \\ simp [bitstringTheory.testbit, bitstringTheory.el_field,
           bitstringTheory.el_w2v]
  )

(* ------------------------------------------------------------------------ *)

val get_bytes = Q.store_thm("get_bytes",
   `((31 >< 24)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b31; b30; b29; b28; b27; b26; b25; b24]: word8) /\
    ((23 >< 16)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b23; b22; b21; b20; b19; b18; b17; b16]: word8) /\
    ((15 >< 8)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b15; b14; b13; b12; b11; b10; b9;  b8]: word8) /\
    ((7 >< 0)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word8)`,
   blastLib.BBLAST_TAC
   )

(* ------------------------------------------------------------------------ *)

val get_vfp_imm32 = Q.store_thm("get_vfp_imm32",
   `(31 >< 0)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word64) =
     v2w [b31; b30; b29; b28; b27; b26; b25; b24;
          b23; b22; b21; b20; b19; b18; b17; b16;
          b15; b14; b13; b12; b11; b10; b9;  b8;
          b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32`,
   blastLib.BBLAST_TAC
   )

val VFPExpandImm = Q.store_thm("VFPExpandImm",
   `VFPExpandImm
       ((v2w [b7; b6; b5; b4]:word4) @@ (v2w [b3; b2; b1; b0]:word4),b) =
    if b then
       v2w [b7; ~b6; b6; b6; b6; b6; b6; b5; b4; b3; b2; b1; b0;
            F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F]
    else
       v2w [b7; ~b6; b6; b6; b6; b6; b6; b6; b6; b6; b5; b4; b3; b2; b1; b0;
            F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F]`,
    lrw [VFPExpandImm_def]
    \\ blastLib.BBLAST_TAC
    )

val fpscr_nzcv = Q.store_thm("fpscr_nzcv",
   `!x:word4 fpscr.
      rec'FPSCR (bit_field_insert 31 28 x (reg'FPSCR fpscr)) =
      fpscr with <| N := x ' 3; Z := x ' 2; C := x ' 1; V := x ' 0 |>`,
   utilsLib.REC_REG_BIT_FIELD_INSERT_TAC "arm" "FPSCR" `fpscr`
   )

val reg_fpscr = Theory.save_thm("reg_fpscr", utilsLib.mk_reg_thm "arm" "FPSCR")

(* ------------------------------------------------------------------------ *)

val v2w_13_15_rwts = Q.store_thm("v2w_13_15_rwts",
   `((v2w [F; b2; b1; b0] = 13w: word4) = F) /\
    ((v2w [b2; F; b1; b0] = 13w: word4) = F) /\
    ((v2w [b2; b1; T; b0] = 13w: word4) = F) /\
    ((v2w [b2; b1; b0; F] = 13w: word4) = F) /\
    ((v2w [F; b2; b1; b0] = 15w: word4) = F) /\
    ((v2w [b2; F; b1; b0] = 15w: word4) = F) /\
    ((v2w [b2; b1; F; b0] = 15w: word4) = F) /\
    ((v2w [b2; b1; b0; F] = 15w: word4) = F)`,
    blastLib.BBLAST_TAC)

fun enumerate_v2w n =
   let
      open Arbnum
      val m = toInt (pow (two, fromInt n))
   in
      List.tabulate
         (m, fn i => bitstringLib.v2w_n2w_CONV
                         (bitstringSyntax.padded_fixedwidth_of_num
                            (Arbnum.fromInt i, n)))
      |> Drule.LIST_CONJ
   end

val v2w_ground4 = Theory.save_thm("v2w_ground4", enumerate_v2w 4)
val v2w_ground5 = Theory.save_thm("v2w_ground5", enumerate_v2w 5)

val bool_not_pc = Q.store_thm("bool_not_pc",
   `~(b3 /\ b2 /\ b1 /\ b0) = (v2w [b3; b2; b1; b0] <> 15w: word4)`,
   blastLib.BBLAST_TAC)

val Decode_simps = Q.prove(
   `((3 >< 0) (0w : word8) = (0w : word4)) /\
    (w2w (v2w [b2; b1; b0] : word3) = v2w [F; b2; b1; b0] : word4) /\
    (w2w ((v2w [b5] : word1) @@ (v2w [b4; b3; b2; b1; b0] : word5) @@
          (0w : word1)) =
     v2w [b5; b4; b3; b2; b1; b0; F] : word32) /\
    (((v2w [b2] : word1) @@ (v2w [b1] : word1) @@ (v2w [b0] : word1) =
     0w:word3) = ~b2 /\ ~b1 /\ ~b0) /\
    (word_msb (v2w [b3; b2; b1; b0] : word4) = b3) /\
    ((v2w [b3] : word1) @@ v2w [b2; b1; b0] : word3 =
     v2w [b3; b2; b1; b0] : word4) /\
    ((v2w [b4] : word1) @@ v2w [b3; b2; b1; b0] : word4 =
     v2w [b4; b3; b2; b1; b0] : word5) /\
    (v2w [b4; b3; b2; b1] : word4 @@ (v2w [b0] : word1) =
     v2w [b4; b3; b2; b1; b0] : word5) /\
    ((v2w [b3; b2; b1; b0] : word4) <+ 8w = ~b3) /\
    ((v2w [b] : word1) @@ (0w : word1) = v2w [b; F] : word2) /\
    (w2w ((v2w [b7; b6; b5; b4; b3; b2; b1; b0] : word8 @@
           (0w: word2)) : word10) =
     v2w [b7; b6; b5; b4; b3; b2; b1; b0; F; F] : word32) /\
     ((7 >< 4) (v2w [b7; b6; b5; b4; b3; b2; b1; b0] : word8) =
      v2w [b7; b6; b5; b4] : word4) /\
     ((3 >< 0) (v2w [b7; b6; b5; b4; b3; b2; b1; b0] : word8) =
      v2w [b3; b2; b1; b0] : word4)`,
   lrw []
   \\ blastLib.BBLAST_TAC
   )

val Decode_simps = Theory.save_thm ("Decode_simps",
   (Decode_simps ::
    List.tabulate
      (8, fn i => let
                     val w = wordsSyntax.mk_wordii (i, 3)
                  in
                     blastLib.BBLAST_CONV ``v2w [a; b; c] = ^w``
                  end)) |> Drule.LIST_CONJ)

val fpreg_div2 = Q.store_thm("fpreg_div2",
   `v2w [b4; b3; b2; b1; b0] // 2w = v2w [F; b4; b3; b2; b1] : word5`,
   blastLib.BBLAST_TAC)

local
   val lem =
    (SIMP_RULE (srw_ss()) [] o Q.SPECL [`v`, `32`] o
     Thm.INST_TYPE [Type.alpha |-> ``:33``]) bitstringTheory.word_index_v2w
in
   val shift32 = Q.prove(
      `!w:word32 imm.
         ((w2w w : 33 word) << imm) ' 32 = testbit 32 (shiftl (w2v w) imm)`,
      strip_tac
      \\ bitstringLib.Cases_on_v2w `w`
      \\ fs [bitstringTheory.w2v_v2w, bitstringTheory.w2w_v2w,
             bitstringTheory.word_lsl_v2w, bitstringTheory.word_index_v2w,
             lem, markerTheory.Abbrev_def])
end

val Shift_C_LSL_rwt = Q.store_thm("Shift_C_LSL_rwt",
   `!imm2 w C s.
        Shift_C (w: word32, SRType_LSL, imm2, C) s =
        ((w << imm2, if imm2 = 0 then C else ((w2w w : 33 word) << imm2) ' 32),
         s)`,
   lrw [Shift_C_def, LSL_C_def, bitstringTheory.shiftl_replicate_F, shift32]
   )

val Shift_C_DecodeImmShift_rwt = Q.prove(
   `!typ imm5 w C s.
       Shift_C (w: word32,
                FST (DecodeImmShift (typ, imm5)),
                SND (DecodeImmShift (typ, imm5)),
                C) s =
     let amount = w2n imm5 in
       (if typ = 0w
           then if imm5 = 0w
                   then (w, C)
                else (w << amount, ((w2w w : 33 word) << amount) ' 32)
        else if typ = 1w
           then if imm5 = 0w
                   then (0w, word_msb w)
                else (w >>> amount, amount <= 32 /\ word_bit (amount - 1) w)
        else if typ = 2w
           then if imm5 = 0w
                   then (w >> 32, word_msb w)
                 else (w >> amount, word_bit (MIN 32 amount - 1) w)
        else if imm5 = 0w
           then SWAP (word_rrx (C, w))
        else (w #>> amount, word_msb (w #>> amount)), s)`,
   strip_tac
   \\ wordsLib.Cases_on_word_value `typ`
   \\ simp [Shift_C_def, LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def, RRX_C_def,
            DecodeImmShift_def, pairTheory.SWAP_def, shift32]
   \\ lrw [wordsTheory.word_rrx_def, wordsTheory.word_bit_def,
           wordsTheory.word_msb_def, wordsTheory.word_lsb_def,
           bitstringTheory.shiftl_replicate_F]
   \\ fs []
   \\ blastLib.BBLAST_TAC
   \\ simp [bitstringTheory.testbit, bitstringTheory.el_field,
            bitstringTheory.el_w2v])
   |> Q.SPEC `v2w [a; b]: word2`
   |> Conv.CONV_RULE
        (Conv.STRIP_QUANT_CONV
           (Conv.RHS_CONV
                (pairLib.let_CONV
                 THENC Conv.DEPTH_CONV bitstringLib.v2w_eq_CONV)))
   |> Drule.GEN_ALL
   |> save_as "Shift_C_DecodeImmShift_rwt"

val Shift_C_DecodeRegShift_rwt = Q.prove(
   `!typ amount w C s.
       Shift_C (w: word32, DecodeRegShift typ, amount, C) s =
       (if typ = 0w
           then (w << amount,
                 if amount = 0 then C else ((w2w w : 33 word) << amount) ' 32)
        else if typ = 1w
           then (w >>> amount,
                 if amount = 0 then C
                 else amount <= 32 /\ word_bit (amount - 1) w)
        else if typ = 2w
           then (w >> amount,
                 if amount = 0 then C else word_bit (MIN 32 amount - 1) w)
        else (w #>> amount,
              if amount = 0 then C else word_msb (w #>> amount)), s)`,
   strip_tac
   \\ wordsLib.Cases_on_word_value `typ`
   \\ simp [Shift_C_def, LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def, RRX_C_def,
            DecodeRegShift_def, shift32]
   \\ lrw [wordsTheory.word_bit_def, bitstringTheory.shiftl_replicate_F,
           wordsTheory.word_msb_def, wordsTheory.word_lsb_def]
   \\ fs [])
   |> Q.SPEC `v2w [a; b]: word2`
   |> Conv.CONV_RULE
        (Conv.STRIP_QUANT_CONV
           (Conv.RHS_CONV (Conv.DEPTH_CONV bitstringLib.v2w_eq_CONV)))
   |> Drule.GEN_ALL
   |> save_as "Shift_C_DecodeRegShift_rwt"

val FST_SWAP = Q.store_thm("FST_SWAP",
   `!x. FST (SWAP x) = SND x`,
   Cases \\ simp [pairTheory.SWAP_def]
   )

val ArchVersion_rwts = Q.prove(
   `(!s. ArchVersion () s < 6 =
         (s.Architecture = ARMv4) \/
         (s.Architecture = ARMv4T) \/
         (s.Architecture = ARMv5T) \/
         (s.Architecture = ARMv5TE)) /\
    (!s. ArchVersion () s >= 5 =
         (s.Architecture <> ARMv4) /\
         (s.Architecture <> ARMv4T)) /\
    (!s. (ArchVersion () s = 4) =
         ((s.Architecture = ARMv4) \/
          (s.Architecture = ARMv4T))) /\
    (!s. ArchVersion () s >= 6 =
         ((s.Architecture = ARMv6) \/
          (s.Architecture = ARMv6K) \/
          (s.Architecture = ARMv6T2) \/
          (s.Architecture = ARMv7_A) \/
          (s.Architecture = ARMv7_R))) /\
    (!s. ArchVersion () s >= 7 =
         ((s.Architecture = ARMv7_A) \/
          (s.Architecture = ARMv7_R)))`,
    lrw [ArchVersion_def] \\ Cases_on `s.Architecture` \\ lfs [])
    |> SIMP_RULE (srw_ss()) []
    |> save_as "ArchVersion_rwts"

val CurrentInstrSet_rwt = Q.prove(
   `((CurrentInstrSet x s = InstrSet_ARM) = ~s.CPSR.J /\ ~s.CPSR.T) /\
    ((CurrentInstrSet x s = InstrSet_Thumb) = ~s.CPSR.J /\ s.CPSR.T) /\
    ((CurrentInstrSet x s = InstrSet_Jazelle) = s.CPSR.J /\ ~s.CPSR.T) /\
    ((CurrentInstrSet x s = InstrSet_ThumbEE) = s.CPSR.J /\ s.CPSR.T)`,
   lrw [CurrentInstrSet_def, ISETSTATE_def, bitstringTheory.word_concat_v2w]
   \\ blastLib.FULL_BBLAST_TAC
   )

fun after_srw tm =
   boolSyntax.rhs (Thm.concl (Conv.QCONV (SIMP_CONV (srw_ss()) []) tm))

val CurrentInstrSet_rwt = Theory.save_thm("CurrentInstrSet_rwt",
   REWRITE_RULE [ASSUME (after_srw ``~s.CPSR.J``)]
     (SIMP_RULE (srw_ss()) [] CurrentInstrSet_rwt))

(* ------------------------------------------------------------------------ *)

val merge_cond = Theory.save_thm("merge_cond",
   METIS_PROVE []
     ``(if x then a:'a else if y then a else b) = (if x \/ y then a else b)``)

val not_cond = Theory.save_thm("not_cond",
   METIS_PROVE [] ``(if ~b then c:'a else d) = (if b then d else c)``)

val isnot15 = Theory.save_thm("isnot15",
  blastLib.BBLAST_PROVE
    ``(n = 0w) \/ (n = 1w) \/ (n = 2w) \/ (n = 3w) \/
      (n = 4w) \/ (n = 5w) \/ (n = 6w) \/ (n = 7w) \/ (n = 8w) \/
      (n = 9w) \/ (n = 10w) \/ (n = 11w) \/ (n = 12w) \/ (n = 13w) \/
      (n = 14w : word4) = (n <> 15w)``)

val mustbe15 = Q.store_thm("mustbe15",
   `!w:word4.
     (if w = 0w then c0 else if w = 1w then c1 else if w = 2w then c2 else
      if w = 3w then c3 else if w = 4w then c4 else if w = 5w then c5 else
      if w = 6w then c6 else if w = 7w then c7 else if w = 8w then c8 else
      if w = 9w then c9 else if w = 10w then c10 else if w = 11w then c11 else
      if w = 12w then c12 else if w = 13w then c13 else if w = 14w then c14 else
      if w = 15w then c15 else c16) =
     (if w = 0w then c0 else if w = 1w then c1 else if w = 2w then c2 else
      if w = 3w then c3 else if w = 4w then c4 else if w = 5w then c5 else
      if w = 6w then c6 else if w = 7w then c7 else if w = 8w then c8 else
      if w = 9w then c9 else if w = 10w then c10 else if w = 11w then c11 else
      if w = 12w then c12 else if w = 13w then c13 else if w = 14w then c14 else
                      c15)`,
   rw [] \\ blastLib.FULL_BBLAST_TAC
   )

(* ------------------------------------------------------------------------ *)

local
   val t = ``LDM_UPTO f i r (b, s)``
in
   val LDM_UPTO_components =
      Drule.LIST_CONJ
         (List.map (GEN_ALL o SIMP_CONV (srw_ss()) [LDM_UPTO_def])
            [``FST ^t``, ``(SND ^t).MEM``, ``(SND ^t).CPSR``,
             ``(SND ^t).Architecture``, ``(SND ^t).Extensions``])
      |> save_as "LDM_UPTO_components"
end

local
   val LDM1_PC = Q.prove(
      `!n b registers s r m.
          n < 15 ==>
          (LDM1 (R_mode m) b registers s r n RName_PC = r RName_PC)`,
      REPEAT strip_tac
      \\ RULE_ASSUM_TAC (Conv.CONV_RULE wordsLib.LESS_CONV)
      \\ full_simp_tac bool_ss []
      \\ fs [R_mode_def, LDM1_def, combinTheory.UPDATE_def]
      \\ lrw [])
in
   val LDM_UPTO_PC = Q.store_thm("LDM_UPTO_PC",
      `!b r s m. FOLDL (LDM1 (R_mode m) b r s) s.REG (COUNT_LIST 15) RName_PC =
                 s.REG RName_PC`,
      rw [EVAL ``COUNT_LIST 15``, LDM1_PC])
end

val LDM_UPTO_RUN = Q.store_thm("LDM_UPTO_RUN",
   `!l f b r s c w u reg.
       FOLDL (LDM1 f b r
         (s with <|CurrentCondition := c; Encoding := w; undefined := u|>))
         reg l =
       FOLDL (LDM1 f b r s) reg l`,
   Induct \\ lrw [LDM1_def]);

local
   val rearrange = Q.prove(
      `(b + if P then 4w else 0w,
        s with REG := (if P then (x =+ y) else I) s.REG) =
       (if P then
           (b + 4w, s with REG := (x =+ y) s.REG)
        else
           (b, s))`,
      lrw [updateTheory.APPLY_UPDATE_ID] \\ lrw [arm_state_component_equality])
      |> Drule.GEN_ALL
in
   val LDM_UPTO_0 =
      ``LDM_UPTO f 0 registers (b, s)``
      |> SIMP_CONV (srw_ss()++boolSimps.LET_ss)
            [bit_count_upto_1, LDM_UPTO_def, LDM1_def, EVAL ``COUNT_LIST 1``,
             rearrange]
      |> Conv.GSYM
      |> save_as "LDM_UPTO_0"
end

val LDM_UPTO_SUC =
   Q.prove(
      `!n f registers b s.
        n < 15 ==>
        ((let x = LDM_UPTO f n registers (b, s) in
          if word_bit (SUC n) registers then
            (FST x + 4w,
             SND x with REG := LDM1 f b registers s ((SND x).REG) (SUC n))
          else
            x) = LDM_UPTO f (SUC n) registers (b, s))`,
      lrw [LDM_UPTO_def, DECIDE ``SUC n + 1 = SUC (n + 1)``,
           wordsTheory.bit_count_upto_def, sum_numTheory.SUM_def,
           wordsTheory.WORD_MULT_SUC, wordsTheory.word_bit_def]
      \\ RULE_ASSUM_TAC (REWRITE_RULE [arithmeticTheory.ADD1])
      \\ fs [rich_listTheory.COUNT_LIST_SNOC, listTheory.FOLDL_SNOC,
             GSYM arithmeticTheory.ADD1]
      \\ CONV_TAC (Conv.RHS_CONV (ONCE_REWRITE_CONV [LDM1_def]))
      \\ simp [wordsTheory.word_bit_def])
   |> SIMP_RULE (bool_ss++boolSimps.LET_ss)
        [numTheory.NOT_SUC, arithmeticTheory.SUC_SUB1, LDM1_def,
         LDM_UPTO_components]
   |> save_as "LDM_UPTO_SUC"

(* ------------------------------------------------------------------------ *)

local
   val t = ``STM_UPTO f i r (b, s)``
in
   val STM_UPTO_components =
      Drule.LIST_CONJ
         (List.map (GEN_ALL o SIMP_CONV (srw_ss()) [STM_UPTO_def])
            [``FST ^t``, ``(SND ^t).REG``, ``(SND ^t).CPSR``,
             ``(SND ^t).Extensions``])
      |> save_as "STM_UPTO_components"
end

val STM_UPTO_RUN = Q.store_thm("STM_UPTO_RUN",
   `!l f b r s c w u mem.
       FOLDL (STM1 f b r
         (s with <|CurrentCondition := c; Encoding := w; undefined := u|>))
         mem l =
       FOLDL (STM1 f b r s) mem l`,
   Induct \\ lrw [STM1_def]);

local
   val rearrange = Q.prove(
      `(b + if P then 4w else 0w,
        s with MEM := (if P then x else I) s.MEM) =
       (if P then
           (b + 4w, s with MEM := x s.MEM)
        else
           (b, s))`,
      lrw [updateTheory.APPLY_UPDATE_ID] \\ lrw [arm_state_component_equality])
      |> Drule.GEN_ALL
in
   val STM_UPTO_0 =
      ``STM_UPTO f 0 registers (b, s)``
      |> SIMP_CONV (srw_ss()++boolSimps.LET_ss)
            [bit_count_upto_1, STM_UPTO_def, STM1_def, EVAL ``COUNT_LIST 1``,
             rearrange]
      |> Conv.GSYM
      |> save_as "STM_UPTO_0"
end

val STM_UPTO_SUC =
   Q.prove(
      `!n f registers b s.
        n < 15 ==>
        ((let x = STM_UPTO f n registers (b, s) in
          if word_bit (SUC n) registers then
            (FST x + 4w,
             SND x with MEM := STM1 f b registers s ((SND x).MEM) (SUC n))
          else
            x) = STM_UPTO f (SUC n) registers (b, s))`,
      lrw [STM_UPTO_def, DECIDE ``SUC n + 1 = SUC (n + 1)``,
           wordsTheory.bit_count_upto_def, sum_numTheory.SUM_def,
           wordsTheory.WORD_MULT_SUC, wordsTheory.word_bit_def]
      \\ RULE_ASSUM_TAC (REWRITE_RULE [arithmeticTheory.ADD1])
      \\ fs [rich_listTheory.COUNT_LIST_SNOC, listTheory.FOLDL_SNOC,
             GSYM arithmeticTheory.ADD1]
      \\ CONV_TAC (Conv.RHS_CONV (ONCE_REWRITE_CONV [STM1_def]))
      \\ simp [wordsTheory.word_bit_def]
      )
   |> SIMP_RULE (bool_ss++boolSimps.LET_ss)
        [numTheory.NOT_SUC, arithmeticTheory.SUC_SUB1, STM1_def,
         STM_UPTO_components, combinTheory.o_THM]
   |> save_as "STM_UPTO_SUC"

(* ------------------------------------------------------------------------ *)

val () = export_theory ()
