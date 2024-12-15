(* ------------------------------------------------------------------------
   Definitions and theorems used by ARM step evaluator (arm_stepLib)
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib

open utilsLib
open wordsLib blastLib
open state_transformerTheory updateTheory alignmentTheory arm8Theory

val _ = new_theory "arm8_step"
val _ = ParseExtras.temp_loose_equality()
(* ------------------------------------------------------------------------ *)

val _ = List.app (fn f => f ())
   [numLib.temp_prefer_num, wordsLib.prefer_word, wordsLib.guess_lengths]

(* ------------------------------------------------------------------------ *)

val NextStateARM8_def = Define`
   NextStateARM8 s0 =
     let s1 = Next s0 in if s1.exception = NoException then SOME s1 else NONE`

val NextStateARM8 = ustore_thm("NextStateARM8",
  `(s.exception = NoException) ==>
   (Fetch (s with branch_hint := NONE) = (w, s with branch_hint := NONE)) /\
   (Decode w = ast) /\
   (!s. Run ast s = f x s) /\
   (f x (s with branch_hint := NONE) = s1) /\
   (s1.exception = s.exception) ==>
   (NextStateARM8 s = SOME (if s1.branch_hint = NONE then
                               s1 with <| PC := s1.PC + 4w |>
                            else s1))`,
   lrw [NextStateARM8_def, Next_def]
   )

(* ------------------------------------------------------------------------ *)

val mem_half_def = Define`
   mem_half (m:word64 -> word8) a = (m (a + 1w) @@ m a) : word16`

val mem_word_def = Define`
   mem_word (m:word64 -> word8) a =
     (m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a) : word32`

val mem_dword_def = Define`
   mem_dword (m:word64 -> word8) a =
     (m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
      m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a) : word64`

(* ------------------------------------------------------------------------ *)

fun concat_tac l =
  ntac (List.length l) strip_tac
  \\ map_every bitstringLib.Cases_on_v2w l
  \\ lfs [markerTheory.Abbrev_def]
  \\ REPEAT (once_rewrite_tac [bitstringTheory.word_concat_v2w_rwt]
  \\ simp [bitstringTheory.w2v_v2w, bitstringTheory.fixwidth_id_imp])

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

val fields = Q.store_thm("fields",
  `(!w:word8.  v2w (field  7  0 (w2v w)) = w) /\
   (!w:word16. v2w (field 15  8 (w2v w)) = (15 ><  8) w : word8) /\
   (!w:word16. v2w (field  7  0 (w2v w)) = ( 7 ><  0) w : word8) /\
   (!w:word32. v2w (field 31 24 (w2v w)) = (31 >< 24) w : word8) /\
   (!w:word32. v2w (field 23 16 (w2v w)) = (23 >< 16) w : word8) /\
   (!w:word32. v2w (field 15  8 (w2v w)) = (15 ><  8) w : word8) /\
   (!w:word32. v2w (field  7  0 (w2v w)) = ( 7 ><  0) w : word8) /\
   (!w:word64. v2w (field 63 56 (w2v w)) = (63 >< 56) w : word8) /\
   (!w:word64. v2w (field 55 48 (w2v w)) = (55 >< 48) w : word8) /\
   (!w:word64. v2w (field 47 40 (w2v w)) = (47 >< 40) w : word8) /\
   (!w:word64. v2w (field 39 32 (w2v w)) = (39 >< 32) w : word8) /\
   (!w:word64. v2w (field 31 24 (w2v w)) = (31 >< 24) w : word8) /\
   (!w:word64. v2w (field 23 16 (w2v w)) = (23 >< 16) w : word8) /\
   (!w:word64. v2w (field 15  8 (w2v w)) = (15 ><  8) w : word8) /\
   (!w:word64. v2w (field  7  0 (w2v w)) = ( 7 ><  0) w : word8)`,
  REPEAT strip_tac
  \\ bitstringLib.Cases_on_v2w `w`
  \\ simp [bitstringTheory.w2v_v2w, bitstringTheory.word_extract_v2w,
           bitstringTheory.word_bits_v2w, bitstringTheory.w2w_v2w]
  \\ fs [markerTheory.Abbrev_def, bitstringTheory.field_id_imp]
  )

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

val bit_field_insert_thms = Theory.save_thm("bit_field_insert_thms",
   utilsLib.map_conv blastLib.BBLAST_PROVE
      [
       ``!a b. bit_field_insert 15 0 (a: word16) (b: word32) =
               (31 >< 16) b @@ a``,
       ``!a b. bit_field_insert 31 16 (a: word16) (b: word32) =
               a @@ (15 >< 0) b``,
       ``!a b. bit_field_insert 15 0 (a: word16) (b: word64) =
               (63 >< 16) b @@ a``,
       ``!a b. bit_field_insert 31 16 (a: word16) (b: word64) =
               (63 >< 32) b @@ a @@ ((15 >< 0) b)``,
       ``!a b. bit_field_insert 47 32 (a: word16) (b: word64) =
               (63 >< 48) b @@ a @@ ((31 >< 0) b)``,
       ``!a b. bit_field_insert 63 48 (a: word16) (b: word64) =
               a @@ ((47 >< 0) b)``
      ]
   )

val concat_bytes = Q.store_thm("concat_bytes",
   `(!w: word32.
       (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w) /\
    (!w: word32 v: word32.
       (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w @@ v =
          w @@ v) /\
    (!w: word64.
       (63 >< 56) w @@ (55 >< 48) w @@ (47 >< 40) w @@ (39 >< 32) w @@
       (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w)`,
   blastLib.BBLAST_TAC
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
   `!x y carry_in.
      AddWithCarry (x,y,carry_in) =
         let (r, c, v) = add_with_carry (x,y,carry_in) in
            (r, word_msb r, r = 0w, c, v)`,
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

val nzcv = Term.mk_var ("nzcv", ``:bool # bool # bool # bool``)

val SetTheFlags = Theory.save_thm("SetTheFlags",
   SetTheFlags_def
   |> Q.SPECL [`setflags`, `FST ^nzcv`, `FST (SND ^nzcv)`,
               `FST (SND (SND ^nzcv))`, `SND (SND (SND ^nzcv))`]
   |> SIMP_RULE std_ss []
   )

(* ------------------------------------------------------------------------ *)

val Replicate_32_64 = Q.store_thm("Replicate_32_64",
   `(!b. Replicate [b] = if b then 0xFFFFFFFFw else 0w: word32) /\
    (!b. Replicate [b] = if b then 0xFFFFFFFFFFFFFFFFw else 0w: word64)`,
   rw [Replicate_def] \\ EVAL_TAC
   )

val ConditionTest = Theory.save_thm("ConditionTest",
   utilsLib.map_conv
     (REWRITE_CONV [ConditionTest_def] THENC wordsLib.WORD_EVAL_CONV)
     (List.tabulate
        (16, fn i =>
               ``ConditionTest (^(wordsSyntax.mk_wordii (i, 4)), n, z, c, v)``))
   )

val ExtendWord = Theory.save_thm("ExtendWord",
   utilsLib.map_conv (REWRITE_CONV [ExtendWord_def])
      [``ExtendWord (w, T)``, ``ExtendWord (w, F)``]
   )

val ExtendValue_0 = Q.store_thm("ExtendValue_0",
   `(!v: word64. ExtendValue (v, ExtendType_UXTX, 0) = v) /\
    (!v: word32. ExtendValue (w2w v, ExtendType_UXTW, 0) = w2w v: word64)`,
   simp [ExtendValue_def, Extend_def, bitstringTheory.field_id_imp,
         bitstringTheory.shiftl_replicate_F, bitstringTheory.replicate_def]
   \\ blastLib.BBLAST_TAC
   \\ simp [bitstringTheory.testbit_el, bitstringTheory.testbit_geq_len,
            bitstringTheory.length_field, bitstringTheory.el_field,
            bitstringTheory.el_w2v]
   \\ blastLib.BBLAST_TAC
   )

(* ------------------------------------------------------------------------ *)

(*
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
*)

(* ------------------------------------------------------------------------ *)

val Align = Q.store_thm("Align",
   `(!w. Align (w, 1) = align 0 w) /\
    (!w. Align (w, 2) = align 1 w) /\
    (!w. Align (w, 4) = align 2 w) /\
    (!w. Align (w, 8) = align 3 w) /\
    (!w. Align (w, 16) = align 4 w)`,
    simp [arm8Theory.Align_def, alignmentTheory.align_w2n]
    )

val Aligned = Q.store_thm("Aligned",
   `(!w. Aligned (w, 1) = aligned 0 w) /\
    (!w. Aligned (w, 2) = aligned 1 w) /\
    (!w. Aligned (w, 4) = aligned 2 w) /\
    (!w. Aligned (w, 8) = aligned 3 w) /\
    (!w. Aligned (w, 16) = aligned 4 w)`,
    simp [arm8Theory.Aligned_def, Align, alignmentTheory.aligned_def,
          boolTheory.EQ_SYM_EQ]
    )

(* ------------------------------------------------------------------------ *)

val DecodeLogicalOp = Q.store_thm("DecodeLogicalOp",
   `!b1 b0. DecodeLogicalOp (v2w [b1; b0]) =
            (if b1 /\ b0 \/ ~(b1 \/ b0) then LogicalOp_AND
             else if b0 then LogicalOp_ORR
             else LogicalOp_EOR,
             b1 /\ b0)`,
   REWRITE_TAC [DecodeLogicalOp_def] \\ Cases \\ Cases \\ EVAL_TAC
   )

val DecodeRevOp = Q.store_thm("DecodeRevOp",
   `!b1 b0. num2RevOp (w2n (v2w [b1; b0] : word2)) =
            if b1 then if b0 then RevOp_REV64 else RevOp_REV32
            else if b0 then RevOp_REV16
            else RevOp_RBIT`,
   Cases \\ Cases \\ EVAL_TAC \\ REWRITE_TAC [arm8Theory.num2RevOp_thm]
   )

val DecodeInzeroExtend = utilsLib.ustore_thm("DecodeInzeroExtend",
   `~(x0 /\ x1) ==>
    ((if ~x0 /\ ~x1 then (T,T)
      else if ~x0 /\ x1 then (F,F)
      else if x0 /\ ~x1 then (T,F)
      else ARB) = (~x1, ~(x0 \/ x1)))`,
   Cases_on `x1`
   \\ Cases_on `x0`
   \\ EVAL_TAC
   )

val DecodeLem = Q.store_thm("DecodeLem",
   `(!a b c d e f g h i.
        (if a then (if b then c else d, e, f) else (g, h, i)) =
        (if a then if b then c else d else g,
         if a then e else h,
         if a then f else i)) /\
    (!a b. (a \/ b) /\ ~b = a /\ ~b)`,
   rw [] \\ decide_tac
   )

val LoadCheck = Q.store_thm("LoadCheck",
   `!b. ((if b then MemOp_LOAD else MemOp_STORE) <> MemOp_LOAD) = ~b`,
   rw []
   )

(* ------------------------------------------------------------------------ *)

val cond_rand_thms = utilsLib.mk_cond_rand_thms [pairSyntax.fst_tm]

fun datatype_thms thms =
   thms @
   [cond_rand_thms, GSYM mem_half_def, GSYM mem_word_def, GSYM mem_dword_def] @
   utilsLib.datatype_rewrites true "arm8" ["arm8_state"]

val DATATYPE_CONV = REWRITE_CONV (datatype_thms [])
val HYP_DATATYPE_RULE = utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV

val st = ``s: arm8_state``
val EV0 = utilsLib.STEP (datatype_thms, st)
fun EV s thms c tm = utilsLib.save_as s (hd (EV0 thms c [] tm))

val EL0 = [``^st.PSTATE.EL = 0w``]
val NOT_TBIT = [``^st.TCR_EL1.TBI1 = F``, ``^st.TCR_EL1.TBI0 = F``]
val NOT_E0E = [``^st.SCTLR_EL1.E0E = F``]
val NOT_SA0 = [``^st.SCTLR_EL1.SA0 = F``]

(* register access *)

val X_rwt = EV "X_rwt" [X_def] [] ``X n``
val write'X_rwt = EV "write'X_rwt" [write'X_def] [] ``write'X (n, d)``

val SP_rwt = EV "SP_rwt" [SP_def] [EL0] ``SP``
val write'SP_rwt = EV "write'SP_rwt" [write'SP_def] [EL0] ``write'SP d``

val BranchTo_rwt =
   EV "BranchTo_rwt" [BranchTo_def, Hint_Branch_def] [EL0 @ NOT_TBIT]
      ``BranchTo (target, branch_type)``

val CheckSPAlignment_rwt =
   EV "CheckSPAlignment_rwt" [CheckSPAlignment_def, SP_rwt]
       [EL0 @ NOT_SA0]
      ``CheckSPAlignment``

val CheckAlignment_rwt =
   EV "CheckAlignment_rwt" [CheckAlignment_def, SP_rwt]
      [[``Aligned (address:word64, n)``]]
      ``CheckAlignment (address, n, acctype, iswrite)``

val BigEndian_rwt =
   EV "BigEndian_rwt" [BigEndian_def] [EL0 @ NOT_E0E] ``BigEndian``

(* ---------------------------- *)

(* read mem *)

val align_rule =
   utilsLib.ALL_HYP_CONV_RULE
      (SIMP_CONV std_ss [Aligned, alignmentTheory.aligned_0]) o
   HYP_DATATYPE_RULE o hd

fun mem_ev s =
   utilsLib.save_as ("mem" ^ s) o align_rule o
   EV0 [Mem_def, BigEndian_rwt, CheckAlignment_rwt, wordsTheory.WORD_ADD_0,
        state_transformerTheory.FOR_def, state_transformerTheory.BIND_DEF,
        listTheory.APPEND_NIL, bitstringTheory.v2w_w2v,
        concat16, concat32, concat64] [] []

val mem1 = mem_ev "1"
   ``Mem (address, 1, acctype) : arm8_state -> word8 # arm8_state``

val mem2 = mem_ev "2"
   ``Mem (address, 2, acctype) : arm8_state -> word16 # arm8_state``

val mem4 = mem_ev "4"
   ``Mem (address, 4, acctype) : arm8_state -> word32 # arm8_state``

val mem8 = mem_ev "8"
   ``Mem (address, 8, acctype) : arm8_state -> word64 # arm8_state``

(* ---------------------------- *)

(* write mem *)

fun mem_ev s =
  utilsLib.save_as ("write'mem" ^ s) o align_rule o
  EV0 [write'Mem_def, BigEndian_rwt, CheckAlignment_rwt, fields,
       state_transformerTheory.FOR_def, state_transformerTheory.BIND_DEF] [] []

val write'mem1 = mem_ev "1" ``write'Mem (d:word8, address, 1, acctype)``
val write'mem2 = mem_ev "2" ``write'Mem (d:word16, address, 2, acctype)``
val write'mem4 = mem_ev "4" ``write'Mem (d:word32, address, 4, acctype)``
val write'mem8 = mem_ev "8" ``write'Mem (d:word64, address, 8, acctype)``

(* ------------------------------------------------------------------------ *)

val () = export_theory ()
