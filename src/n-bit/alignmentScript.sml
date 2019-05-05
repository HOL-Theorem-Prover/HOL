(* ========================================================================= *)
(* FILE          : alignmentScript.sml                                       *)
(* DESCRIPTION   : Theory for address alignment.                             *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib Q
open wordsLib

val () = new_theory "alignment";

val ERR = mk_HOL_ERR "alignmentScript"

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

Theorem aligned_extract:
   !p w. aligned p (w: 'a word) <=> (p = 0) \/ ((p - 1 >< 0) w = 0w: 'a word)
Proof
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
QED

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

val align_add_aligned = Q.store_thm("align_add_aligned",
  `!p a b : 'a word.
     aligned p a /\ w2n b < 2 ** p ==> (align p (a + b) = a)`,
  strip_tac
  \\ Cases_on `dimindex(:'a) <= p`
  >- (`w2n b < 2 ** p`
      by metis_tac [wordsTheory.w2n_lt, wordsTheory.dimword_def,
                    bitTheory.TWOEXP_MONO2, arithmeticTheory.LESS_LESS_EQ_TRANS]
      \\ simp [aligned_ge_dim, align_w2n, arithmeticTheory.LESS_DIV_EQ_ZERO])
  \\ fs [arithmeticTheory.NOT_LESS_EQUAL]
  \\ rw [aligned_extract, align_sub, wordsTheory.WORD_EXTRACT_COMP_THM,
         arithmeticTheory.MIN_DEF,
         Once (GSYM wordsTheory.WORD_EXTRACT_OVER_ADD2),
         wordsTheory.WORD_EXTRACT_ID
         |> Q.SPECL [`w`, `p - 1`]
         |> Q.DISCH `p <> 0n`
         |> SIMP_RULE std_ss [DECIDE ``p <> 0n ==> (SUC (p - 1) = p)``]
        ]
  \\ fs [DECIDE ``(a < 1n) = (a = 0n)``, wordsTheory.w2n_eq_0]
  )

Theorem lt_align_eq_0:
  w2n a < 2 ** p ==> (align p a = 0w)
Proof
  Cases_on`a` \\ fs[]
  \\ rw[align_w2n]
  \\ Cases_on`p = 0` \\ fs[]
  \\ `1 < 2 ** p` by fs[arithmeticTheory.ONE_LT_EXP]
  \\ `n DIV 2 ** p = 0` by fs[arithmeticTheory.DIV_EQ_0]
  \\ fs[]
QED

Theorem aligned_or:
  aligned n (w || v) <=> aligned n w /\ aligned n v
Proof
  Cases_on `n = 0`
  \\ srw_tac [WORD_BIT_EQ_ss] [aligned_extract]
  \\ metis_tac []
QED

Theorem aligned_w2n:
  aligned k w <=> (w2n (w:'a word) MOD 2 ** k = 0)
Proof
  Cases_on `w`
  \\ fs [aligned_def,align_w2n]
  \\ `0n < 2 ** k` by simp []
  \\ drule arithmeticTheory.DIVISION
  \\ disch_then (qspec_then `n` assume_tac)
  \\ `(n DIV 2 ** k * 2 ** k) < dimword (:'a)` by decide_tac
  \\ asm_simp_tac std_ss [] \\ decide_tac
QED

Theorem MOD_0_aligned:
  !n p. (n MOD 2 ** p = 0) ==> aligned p (n2w n)
Proof
  fs [aligned_bitwise_and]
  \\ once_rewrite_tac [wordsTheory.WORD_AND_COMM]
  \\ fs [wordsTheory.WORD_AND_EXP_SUB1]
QED

Theorem aligned_lsl_leq:
  k <= l ==> aligned k (w << l)
Proof
  fs [aligned_def,align_def]
  \\ fs [fcpTheory.CART_EQ,wordsTheory.word_lsl_def,
         wordsTheory.word_slice_def,fcpTheory.FCP_BETA]
  \\ rw [] \\ eq_tac \\ fs []
QED

Theorem aligned_lsl[simp]:
  aligned k (w << k)
Proof match_mp_tac aligned_lsl_leq \\ fs[]
QED

Theorem align_align_MAX:
  !k l w. align k (align l w) = align (MAX k l) w
Proof
  fs[align_def,fcpTheory.CART_EQ,wordsTheory.word_slice_def,fcpTheory.FCP_BETA]
  \\ rw [] \\ eq_tac \\ fs []
QED

Theorem pow2_eq_0:
  dimindex (:'a) <= k ==> (n2w (2 ** k) = 0w:'a word)
Proof
  fs [wordsTheory.dimword_def] \\ fs [arithmeticTheory.LESS_EQ_EXISTS]
  \\ rw [] \\ fs [arithmeticTheory.EXP_ADD,arithmeticTheory.MOD_EQ_0]
QED

Theorem aligned_pow2:
  aligned k (n2w (2 ** k))
Proof
  Cases_on `k < dimindex (:'a)`
  \\ fs [arithmeticTheory.NOT_LESS,pow2_eq_0,aligned_0]
  \\ `2 ** k < dimword (:'a)` by fs [wordsTheory.dimword_def]
  \\ fs [aligned_def,align_w2n]
QED

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

val aligned_add_sub_123 = save_thm ("aligned_add_sub_123",
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

val () = export_theory ()
