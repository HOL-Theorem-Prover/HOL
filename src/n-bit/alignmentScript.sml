(* ========================================================================= *)
(* FILE          : alignmentScript.sml                                       *)
(* DESCRIPTION   : Theory for address alignment.                             *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib Q
open lcsymtacs
open wordsLib

val () = Theory.new_theory "alignment";

(* -------------------------------------------------------------------------
   Constant definitions
   ------------------------------------------------------------------------- *)

val align_def   = Define `align p (w: 'a word) = (dimindex (:'a) - 1 '' p) w`
val aligned_def = Define `aligned p w = (align p w = w)`

val byte_align_def = Define`
   byte_align (w: 'a word) = align (LOG2 (dimindex(:'a) DIV 8)) w`

val byte_aligned_def = Define`
   byte_aligned (w: 'a word) = aligned (LOG2 (dimindex(:'a) DIV 8)) w`

(* -------------------------------------------------------------------------
   Theorems
   ------------------------------------------------------------------------- *)

val align_0 = Q.store_thm("align_0",
   `!w. align 0 w = w`,
   lrw [wordsTheory.WORD_SLICE_BITS_THM, wordsTheory.WORD_ALL_BITS, align_def]
   )

val align_align = Q.store_thm("align_align",
   `!p w. align p (align p w) = align p w`,
   srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [align_def]
   )

val aligned_align = Q.store_thm ("aligned_align",
   `!p w. aligned p (align p w)`,
   rewrite_tac [aligned_def, align_align]
   )

val align_aligned = Q.store_thm ("align_aligned",
   `!p w. aligned p w ==> (align p w = w)`,
   rewrite_tac [aligned_def]
   )

val align_bitwise_and = Q.store_thm("align_bitwise_and",
   `!p w. align p w = w && UINT_MAXw << p`,
   srw_tac [wordsLib.WORD_BIT_EQ_ss] [align_def]
   \\ decide_tac
   )

val align_shift = Q.store_thm("align_shift",
   `!p w. align p w = w >>> p << p`,
   srw_tac [wordsLib.WORD_BIT_EQ_ss] [align_def]
   \\ Cases_on `p <= i`
   \\ simp []
   )

val align_w2n = Q.store_thm("align_w2n",
   `!p w. align p w = n2w (w2n w DIV 2 ** p * 2 ** p)`,
   strip_tac
   \\ Cases
   \\ lrw [align_shift, GSYM wordsTheory.n2w_DIV, wordsTheory.word_lsl_n2w,
           wordsTheory.dimword_def]
   \\ `dimindex(:'a) <= p` by decide_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ simp [arithmeticTheory.EXP_ADD, arithmeticTheory.MOD_EQ_0]
   )

val ths = [GSYM wordsTheory.WORD_w2w_EXTRACT, wordsTheory.w2w_id]

val lem =
   wordsTheory.EXTRACT_JOIN_ADD
   |> Thm.INST_TYPE [Type.beta |-> Type.alpha]
   |> Q.SPECL [`dimindex(:'a) - 1`, `p - 1`, `p`, `0`, `p`, `w`]
   |> Q.DISCH `0 < p`
   |> SIMP_RULE (srw_ss()) (DECIDE ``0 < p ==> (p = p - 1 + 1)`` :: ths)
   |> GSYM

val align_sub = Q.store_thm("align_sub",
   `!p w. align p w = if p = 0 then w else w - (p - 1 >< 0) w`,
   rw_tac bool_ss [align_0]
   \\ Cases_on `dimindex(:'a) <= p - 1`
   >- (
      `(p - 1 >< 0) w : 'a word = (dimindex (:'a) - 1 >< 0) w`
      by simp [wordsTheory.WORD_EXTRACT_MIN_HIGH]
      \\ rule_assum_tac (SIMP_RULE (srw_ss()) ths)
      \\ asm_rewrite_tac []
      \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [align_def]
      )
   \\ Cases_on `p = dimindex(:'a)`
   >- srw_tac [wordsLib.WORD_BIT_EQ_ss] (align_def :: ths)
   \\ `0 < p /\ p <= dimindex (:'a) - 1` by decide_tac
   \\ imp_res_tac lem
   \\ pop_assum (qspec_then `w` (CONV_TAC o Conv.PATH_CONV "rlr" o Lib.K))
   \\ srw_tac [wordsLib.WORD_EXTRACT_ss] [align_def]
   )

val aligned_extract = Q.store_thm ("aligned_extract",
   `!p w. aligned p (w: 'a word) = (p = 0) \/ ((p - 1 >< 0) w = 0w: 'a word)`,
   rewrite_tac [aligned_def]
   \\ Cases
   >- rewrite_tac [align_0]
   \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [align_def]
   \\ eq_tac
   \\ lrw []
   \\ res_tac
   \\ Cases_on `i <= n`
   \\ Cases_on `w ' i`
   \\ fs []
   \\ decide_tac
   )

val aligned_0 = Q.store_thm ("aligned_0",
   `(!p. aligned p 0w) /\ (!w. aligned 0 w)`,
   srw_tac [wordsLib.WORD_BIT_EQ_ss] [aligned_extract]
   )

val aligned_1_lsb = Q.store_thm ("aligned_1_lsb",
   `!w. aligned 1 w = ~word_lsb w`,
   srw_tac [wordsLib.WORD_BIT_EQ_ss] [aligned_extract]
   )

val aligned_ge_dim = Q.store_thm ("aligned_ge_dim",
   `!p w:'a word. dimindex(:'a) <= p ==> (aligned p w = (w = 0w))`,
   Cases \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [aligned_extract]
   )

val aligned_bitwise_and = Q.store_thm("aligned_bitwise_and",
   `!p w. aligned p (w: 'a word) = (w && n2w (2 ** p - 1) = 0w)`,
   simp [aligned_def, align_bitwise_and]
   \\ srw_tac [wordsLib.WORD_BIT_EQ_ss]
        [wordsTheory.word_index, bitTheory.BIT_EXP_SUB1]
   \\ eq_tac
   \\ lrw []
   \\ res_tac
   \\ Cases_on `i < SUC n`
   \\ Cases_on `w ' i`
   \\ fs []
   \\ decide_tac
   )

val aligned_bit_count_upto = Q.store_thm ("aligned_bit_count_upto",
   `!p w.
     aligned p (w: 'a word) = (bit_count_upto (MIN (dimindex(:'a)) p) w = 0)`,
   lrw [aligned_extract, wordsTheory.bit_count_upto_is_zero]
   \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] []
   \\ Cases_on `p = 0`
   \\ simp []
   \\ eq_tac
   \\ lrw []
   \\ res_tac
   >- decide_tac
   \\ Cases_on `i < p`
   \\ fs []
   \\ decide_tac
   )

val aligned_add_sub = Q.store_thm("aligned_add_sub",
   `!p a: 'a word b.
          aligned p b ==>
          (aligned p (a + b) = aligned p a) /\
          (aligned p (a - b) = aligned p a)`,
   strip_tac
   \\ Cases_on `dimindex(:'a) <= p`
   >- simp [aligned_ge_dim]
   \\ `p < dimindex(:'a)` by decide_tac
   \\ Cases_on `p`
   \\ simp [aligned_extract]
   \\ Cases_on `SUC n = dimindex(:'a)`
   \\ srw_tac [wordsLib.WORD_EXTRACT_ss] []
   \\ simp [Once (GSYM wordsTheory.WORD_EXTRACT_OVER_ADD2),
            Once (GSYM wordsTheory.WORD_EXTRACT_OVER_MUL2)]
   \\ lrw [wordsTheory.WORD_EXTRACT_COMP_THM, arithmeticTheory.MIN_DEF]
   \\ metis_tac [arithmeticTheory.SUC_SUB1]
   )

val aligned_add_sub_cor = Q.store_thm("aligned_add_sub_cor",
   `!p a: 'a word b.
       aligned p a /\ aligned p b ==> aligned p (a + b) /\ aligned p (a - b)`,
   metis_tac [aligned_add_sub]
   )

val aligned_mul_shift_1 = Q.store_thm ("aligned_mul_shift_1",
   `!p w: 'a word. aligned p (1w << p * w)`,
   strip_tac
   \\ Cases_on `dimindex(:'a) <= p`
   >- simp [aligned_ge_dim]
   \\ `p < dimindex(:'a)` by decide_tac
   \\ Cases_on `p`
   \\ srw_tac [ARITH_ss]
        [aligned_extract,
         Once (GSYM wordsTheory.WORD_EXTRACT_OVER_MUL2)]
   \\ `(n >< 0) ((1w:'a word) << SUC n) = 0w: 'a word`
   by lrw [wordsTheory.WORD_MUL_LSL, wordsTheory.word_extract_n2w,
           arithmeticTheory.MIN_DEF,
           bitTheory.BITS_SUM2
           |> Q.SPECL [`n`, `0`, `1`, `0`]
           |> SIMP_RULE (srw_ss()) []]
   \\ simp [wordsTheory.WORD_EXTRACT_COMP_THM, arithmeticTheory.MIN_DEF]
   )

val aligned_add_sub_prod = Q.store_thm("aligned_add_sub_prod",
   `!p w: 'a word x.
      (aligned p (w + (1w << p) * x) = aligned p w) /\
      (aligned p (w - (1w << p) * x) = aligned p w)`,
   metis_tac [aligned_add_sub, aligned_mul_shift_1, wordsTheory.WORD_ADD_COMM]
   )

val aligned_imp = Q.store_thm("aligned_imp",
   `!p q w. p < q /\ aligned q w ==> aligned p w`,
   srw_tac [wordsLib.WORD_BIT_EQ_ss] [aligned_extract]
   >- fs []
   \\ Cases_on `p`
   \\ lrw []
   \\ res_tac
   \\ simp []
   )

(* -------------------------------------------------------------------------
   Theorems for standard alignment lengths of 1, 2 and 3 bits
   ------------------------------------------------------------------------- *)

fun f p =
   let
      val th1 =
         aligned_add_sub_prod
         |> Q.SPEC p
         |> SIMP_RULE std_ss [fcpTheory.DIMINDEX_GE_1, wordsTheory.word_1_lsl]
      val th2 = th1 |> Q.SPEC `0w` |> SIMP_RULE (srw_ss()) [aligned_0]
   in
      [th1, th2]
   end

val aligned_add_sub_123 = Theory.save_thm ("aligned_add_sub_123",
   LIST_CONJ (List.concat (List.map f [`1`, `2`, `3`]))
   )

local
   val bit_lem = Q.prove(
      `(!x. NUMERAL (BIT2 x) = 2 * (x + 1)) /\
       (!x. NUMERAL (BIT1 x) = 2 * x + 1) /\
       (!x. NUMERAL (BIT1 (BIT1 x)) = 4 * x + 3) /\
       (!x. NUMERAL (BIT1 (BIT2 x)) = 4 * (x + 1) + 1) /\
       (!x. NUMERAL (BIT2 (BIT1 x)) = 4 * (x + 1)) /\
       (!x. NUMERAL (BIT2 (BIT2 x)) = 4 * (x + 1) + 2) /\
       (!x. NUMERAL (BIT1 (BIT1 (BIT1 x))) = 8 * x + 7) /\
       (!x. NUMERAL (BIT1 (BIT1 (BIT2 x))) = 8 * (x + 1) + 3) /\
       (!x. NUMERAL (BIT1 (BIT2 (BIT1 x))) = 8 * (x + 1) + 1) /\
       (!x. NUMERAL (BIT1 (BIT2 (BIT2 x))) = 8 * (x + 1) + 5) /\
       (!x. NUMERAL (BIT2 (BIT1 (BIT1 x))) = 8 * (x + 1)) /\
       (!x. NUMERAL (BIT2 (BIT1 (BIT2 x))) = 8 * (x + 1) + 4) /\
       (!x. NUMERAL (BIT2 (BIT2 (BIT1 x))) = 8 * (x + 1) + 2) /\
       (!x. NUMERAL (BIT2 (BIT2 (BIT2 x))) = 8 * (x + 1) + 6)`,
      REPEAT strip_tac
      \\ CONV_TAC (Conv.LHS_CONV
            (REWRITE_CONV [arithmeticTheory.BIT1, arithmeticTheory.BIT2,
                           arithmeticTheory.NUMERAL_DEF]))
      \\ decide_tac
      )
   val (_, _, dest_num, _) = HolKernel.syntax_fns1 "arithmetic" "NUMERAL"
in
   fun bit_lem_conv tm =
      let
         val x = dest_num (fst (wordsSyntax.dest_n2w tm))
      in
         if List.null (Term.free_vars x)
            then raise ERR "bit_lem_conv" ""
         else Conv.RAND_CONV (ONCE_REWRITE_CONV [bit_lem]) tm
      end
end

val aligned_numeric = Q.store_thm("aligned_numeric",
   `(!x. aligned 3 (n2w (NUMERAL (BIT2 (BIT1 (BIT1 x)))))) /\
    (!x. aligned 2 (n2w (NUMERAL (BIT2 (BIT1 x))))) /\
    (!x. aligned 1 (n2w (NUMERAL (BIT2 x)))) /\
    (!x. aligned 3 (-n2w (NUMERAL (BIT2 (BIT1 (BIT1 x)))))) /\
    (!x. aligned 2 (-n2w (NUMERAL (BIT2 (BIT1 x))))) /\
    (!x. aligned 1 (-n2w (NUMERAL (BIT2 x)))) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT1 (BIT1 (BIT1 (f x)))))) =
             aligned 3 (y + 7w)) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT1 (BIT1 (BIT2 x))))) =
             aligned 3 (y + 3w)) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT1 (BIT2 (BIT1 x))))) =
             aligned 3 (y + 1w)) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT1 (BIT2 (BIT2 x))))) =
             aligned 3 (y + 5w)) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT2 (BIT1 (BIT1 x))))) =
             aligned 3 (y)) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT2 (BIT1 (BIT2 x))))) =
             aligned 3 (y + 4w)) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT2 (BIT2 (BIT1 x))))) =
             aligned 3 (y + 2w)) /\
    (!x y f. aligned 3 (y + n2w (NUMERAL (BIT2 (BIT2 (BIT2 x))))) =
             aligned 3 (y + 6w)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT1 (BIT1 (BIT1 (f x)))))) =
             aligned 3 (y - 7w)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT1 (BIT1 (BIT2 x))))) =
             aligned 3 (y - 3w)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT1 (BIT2 (BIT1 x))))) =
             aligned 3 (y - 1w)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT1 (BIT2 (BIT2 x))))) =
             aligned 3 (y - 5w)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT2 (BIT1 (BIT1 x))))) =
             aligned 3 (y)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT2 (BIT1 (BIT2 x))))) =
             aligned 3 (y - 4w)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT2 (BIT2 (BIT1 x))))) =
             aligned 3 (y - 2w)) /\
    (!x y f. aligned 3 (y - n2w (NUMERAL (BIT2 (BIT2 (BIT2 x))))) =
             aligned 3 (y - 6w)) /\
    (!x y f. aligned 2 (y + n2w (NUMERAL (BIT1 (BIT1 (f x))))) =
             aligned 2 (y + 3w)) /\
    (!x y. aligned 2 (y + n2w (NUMERAL (BIT1 (BIT2 x)))) =
           aligned 2 (y + 1w)) /\
    (!x y. aligned 2 (y + n2w (NUMERAL (BIT2 (BIT1 x)))) =
           aligned 2 (y)) /\
    (!x y. aligned 2 (y + n2w (NUMERAL (BIT2 (BIT2 x)))) =
           aligned 2 (y + 2w)) /\
    (!x y f. aligned 2 (y - n2w (NUMERAL (BIT1 (BIT1 (f x))))) =
             aligned 2 (y - 3w)) /\
    (!x y. aligned 2 (y - n2w (NUMERAL (BIT1 (BIT2 x)))) =
           aligned 2 (y - 1w)) /\
    (!x y. aligned 2 (y - n2w (NUMERAL (BIT2 (BIT1 x)))) =
           aligned 2 (y)) /\
    (!x y. aligned 2 (y - n2w (NUMERAL (BIT2 (BIT2 x)))) =
           aligned 2 (y - 2w)) /\
    (!x y f. aligned 1 (y + n2w (NUMERAL (BIT1 (f x)))) =
             aligned 1 (y + 1w)) /\
    (!x y f. aligned 1 (y - n2w (NUMERAL (BIT1 (f x)))) =
             aligned 1 (y - 1w)) /\
    (!x y. aligned 1 (y + n2w (NUMERAL (BIT2 x))) = aligned 1 y) /\
    (!x y. aligned 1 (y - n2w (NUMERAL (BIT2 x))) = aligned 1 y)`,
   REPEAT strip_tac
   \\ CONV_TAC (DEPTH_CONV bit_lem_conv)
   \\ rewrite_tac
        [GSYM wordsTheory.word_mul_n2w, GSYM wordsTheory.word_add_n2w,
         wordsLib.WORD_DECIDE ``a + (b * c + d) : 'a word = (a + d) + b * c``,
         wordsLib.WORD_DECIDE ``a - (b * c + d) : 'a word = (a - d) - b * c``,
         wordsTheory.WORD_NEG_LMUL, aligned_add_sub_123]
   )

(* ------------------------------------------------------------------------- *)

val () = Theory.export_theory ()
