structure wordsLib :> wordsLib =
struct

(* interactive use:
  app load ["fcpLib", "numeral_bitTheory", "wordsTheory", "wordsSyntax"];
*)

open HolKernel Parse boolLib bossLib computeLib;
open bitTheory numeral_bitTheory wordsTheory wordsSyntax;

val ISPEC = Q.ISPEC;
val SPEC  = Q.SPEC;
val SPECL = Q.SPECL;;
val INST  = Q.INST;

(* ------------------------------------------------------------------------- *)

fun is_fcp_thm s =
  not (s = "dimword_IS_TWICE_INT_MIN" orelse s = "INT_MIN_SUM") andalso
  (String.isPrefix "finite_" s orelse String.isPrefix "dimindex_" s orelse
   String.isPrefix "dimword_" s orelse String.isPrefix "INT_MIN_" s);

val machine_sizes = (map snd o filter (is_fcp_thm o fst) o theorems) "words";

val sizes_comp = new_compset machine_sizes;

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

local
  val compset = reduceLib.num_compset()
  val _ = add_thms [NUMERAL_SFUNPOW_FDUB, NUMERAL_SFUNPOW_iDUB, iDUB_NUMERAL,
                    FDUB_iDUB, FDUB_FDUB, NUMERAL_TIMES_2EXP] compset
  val conv = CBV_CONV compset
  val rule = REWRITE_RULE [TIMES_2EXP1, arithmeticTheory.TIMES2,
                           GSYM numeralTheory.iDUB]
in
  fun SIZES_CONV t =
    let val rtr = fst (dest_const (rator t)) handle HOL_ERR _ => ""
    in
      if (rtr = "dimword") orelse (rtr = "dimindex") orelse
         (rtr = "INT_MIN") orelse (rtr = "FINITE")
      then
        CHANGED_CONV (CBV_CONV sizes_comp) t
          handle HOL_ERR _ =>
            let val x = (PURE_REWRITE_CONV [rule INT_MIN_def,
                                            rule dimword_IS_TWICE_INT_MIN]
                           THENC fcpLib.INDEX_CONV THENC conv) t
                val _ = add_thms [x] sizes_comp
            in
              x
            end
      else
        failwith "Term not: dimword, dimindex, INT_MIN or FINITE"
    end
end;

fun size_conv t = {conv = K (K (SIZES_CONV)), trace = 3,
                   name = "SIZES_CONV", key = SOME ([], t)};

val SIZES_ss = simpLib.merge_ss (rewrites [ONE_LT_dimword, DIMINDEX_GT_0]::
  (map (simpLib.conv_ss o size_conv)
    [``dimindex(:'a)``, ``FINITE (UNIV:'a set)``,
     ``INT_MIN(:'a)``, ``dimword(:'a)``]));

fun NUM_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ
     ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss l o INST [n |-> `0`]) y)
     ((GEN_ALL o INST [n |-> `NUMERAL n`]) y)
  end;

val MOD_WL =
  (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))));

val MOD_WL1 =
  (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (RATOR_CONV
   (ONCE_REWRITE_CONV [GSYM n2w_mod])))));

val thms =
  [numeralTheory.numeral_funpow, pairTheory.UNCURRY_DEF,
   iBITWISE, NUMERAL_BITWISE, LSB_def, BITV_def, SIGN_EXTEND_def, SBIT_def,
   DIVMOD_2EXP, NUMERAL_DIV_2EXP, NUMERAL_TIMES_2EXP, NUMERAL_iDIV2,
   NUMERAL_SFUNPOW_iDIV2,NUMERAL_SFUNPOW_iDUB,NUMERAL_SFUNPOW_FDUB,
   FDUB_iDIV2,FDUB_iDUB,FDUB_FDUB,
   NUMERAL_BIT_MODIFY, NUMERAL_BIT_MODF,
   NUMERAL_BIT_REVERSE, NUMERAL_BIT_REV,
   NUM_RULE [NUMERAL_DIV_2EXP,numeralTheory.MOD_2EXP] `n` BITS_def,
   NUM_RULE [NUMERAL_DIV_2EXP,numeralTheory.MOD_2EXP] `n` SLICE_def,
   NUM_RULE [BITS_ZERO2] `n`  BIT_def, INT_MIN_SUM,
   numeral_log2,numeral_ilog2,
   n2w_11, n2w_w2n, w2n_n2w, MOD_WL1 w2w_n2w, sw2sw_def, word_len_def,
   word_L_def, word_H_def, word_T_def,
   word_join_def, word_concat_def,
   word_reverse_n2w, word_modify_n2w, word_log2_n2w,
   word_1comp_n2w, word_or_n2w, word_xor_n2w, word_and_n2w,
   word_2comp_n2w, word_sub_def, word_div_def, word_sdiv_def,
   MOD_WL word_add_n2w, MOD_WL word_mul_n2w,
   word_asr_n2w, word_lsr_n2w, word_lsl_n2w,
   (List.last o CONJUNCTS) SHIFT_ZERO, SPEC `NUMERAL n` word_ror_n2w,
   word_rol_def, word_rrx_n2w,
   word_lsb_n2w, word_msb_n2w, word_bit_n2w, word_index_n2w,
   word_bits_n2w, word_slice_n2w, fcp_n2w, word_extract_n2w,
   word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
   word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w];

val thms =
  let fun mrw th = map (REWRITE_RULE [th])
in
    (mrw TIMES_2EXP1 o mrw (GSYM bitTheory.TIMES_2EXP_def) o
     mrw (GSYM arithmeticTheory.MOD_2EXP_def)) thms
end;

fun words_compset () =
  let val compset = reduceLib.num_compset()
      val _ = add_thms thms compset
      val _ = add_conv(``dimindex:'a itself -> num``, 1, SIZES_CONV) compset
      val _ = add_conv(``dimword:'a itself -> num``, 1, SIZES_CONV) compset
      val _ = add_conv(``INT_MIN:'a itself -> num``, 1, SIZES_CONV) compset
in
  compset
end;

val _ = add_thms thms the_compset;
val _ = add_conv(``dimindex:'a itself -> num``, 1, SIZES_CONV) the_compset;
val _ = add_conv(``dimword:'a itself -> num``, 1, SIZES_CONV) the_compset;
val _ = add_conv(``INT_MIN:'a itself -> num``, 1, SIZES_CONV) the_compset;

val WORD_EVAL_CONV = CBV_CONV (words_compset());
val WORD_EVAL_RULE = CONV_RULE WORD_EVAL_CONV;
val WORD_EVAL_TAC  = CONV_TAC WORD_EVAL_CONV;

(* ------------------------------------------------------------------------- *)
(* Simpsets                                                                  *)
(* ------------------------------------------------------------------------- *)

val alpha_rws =
  [word_lsb_n2w, word_lsb_word_T, word_msb_0, word_msb_word_T, WORD_L_NEG,
   word_bit_0, word_bit_0_word_T, w2w_0, sw2sw_0, sw2sw_word_T,
   word_0_n2w, word_1_n2w,
   word_reverse_0, word_reverse_word_T, word_log2_1, word_div_1,
   word_join_0, word_concat_0, word_concat_word_T, word_join_word_T,
   WORD_BITS_ZERO2, WORD_EXTRACT_ZERO2, WORD_SLICE_ZERO2,
   (REWRITE_RULE [LSB_ODD] o GSYM) LSB_def, BIT_ZERO, BITS_ZERO2];

val is_known_word_size = not o is_vartype o wordsSyntax.dim_of;

fun UINT_MAX_CONV t =
  if wordsSyntax.is_n2w t andalso is_known_word_size t then
    let val thm = EVAL (wordsSyntax.mk_word_T (wordsSyntax.dim_of t)) in
      PURE_REWRITE_CONV [GSYM thm, SYM WORD_NEG_1] t
    end
  else
   raise UNCHANGED;

fun WORD_GROUND_CONV t =
let
  val _ = null (type_vars_in_term t) orelse failwith "Contains type variables."
in
  (computeLib.CBV_CONV (words_compset()) THENC UINT_MAX_CONV) t
end;

val pats =
  [``sw2sw (n2w (NUMERAL a) :'a word) : 'b word``,
   ``word_reverse (n2w (NUMERAL a) :'a word)``,
   ``word_len (a:'a word)``,
   ``word_msb (n2w (NUMERAL a) :'a word)``,
   ``word_join (0w:'b word) (x :'a word)``,
   ``word_bit 0 (n2w (NUMERAL a) :'a word)``,
   ``(n2w (NUMERAL a) :'a word) >> (NUMERAL n)``,
   ``(n2w (NUMERAL a) :'a word) #>> (NUMERAL n)``,
   ``(w :'a word) #<< (NUMERAL n)``,
   ``word_rrx (F, n2w (NUMERAL a) :'a word)``,
   ``word_rrx (T, n2w (NUMERAL a) :'a word)``,
   ``(n2w (NUMERAL a) :'a word) <+ (n2w (NUMERAL b))``,
   ``(n2w (NUMERAL a) :'a word) <=+ (n2w (NUMERAL b))``,
   ``(0w:'a word) <+ (n2w (NUMERAL b))``,
   ``(0w:'a word) < (n2w (NUMERAL b))``,
   ``(0w:'a word) <= (n2w (NUMERAL b))``,
   ``(n2w (NUMERAL a) :'a word) < 0w``,
   ``(n2w (NUMERAL a) :'a word) <= 0w``,
   ``BIT (NUMERAL a) (NUMERAL b)``,
   ``BITS 0 0 (NUMERAL b)``,
   ``BITS 0 (NUMERAL a) (NUMERAL b)``,
   ``BITS (NUMERAL a) 0 (NUMERAL b)``,
   ``BITS (NUMERAL a) (NUMERAL b) (NUMERAL c)``,
   ``TIMES_2EXP 0 a``,
   ``TIMES_2EXP (NUMERAL a) b``,
   ``DIV_2EXP 0 a``,
   ``DIV_2EXP (NUMERAL a) b``
  ] @ List.concat
   (map (fn th => [subst [``x :'a word`` |-> ``n2w (NUMERAL a) :'a word``] th,
                   subst [``x :'a word`` |-> ``$- 1w :'a word``] th])
     [
      ``w2w (x :'a word) : 'b word``,
      ``w2n (x :'a word)``,
      ``word_log2 (x :'a word)``,
      ``word_join (x :'a word) (0w:'b word)``,
      ``word_concat (0w:'b word) (x :'a word) : 'c word``,
      ``word_concat (x :'a word) (0w:'b word) : 'c word``,
      ``word_bit (NUMERAL n) (x :'a word)``,
      ``((NUMERAL n) -- 0) (x :'a word)``,
      ``((NUMERAL m) -- (NUMERAL n)) (x :'a word)``,
      ``((NUMERAL n) <> 0) (x :'a word)``,
      ``((NUMERAL m) <> (NUMERAL n)) (x :'a word)``,
      ``((NUMERAL n) >< 0) (x :'a word) : 'b word``,
      ``((NUMERAL m) >< (NUMERAL n)) (x :'a word) : 'b word``,
      ``(x :'a word) << (NUMERAL n)``,
      ``(x :'a word) >>> (NUMERAL n)``
     ]) @ List.concat
   (map (fn th => [subst [``x :'a word`` |-> ``n2w (NUMERAL a) :'a word``,
                          ``y :'b word`` |-> ``$- 1w :'b word``] th,
                   subst [``x :'a word`` |-> ``$- 1w :'a word``,
                          ``y :'b word`` |-> ``n2w (NUMERAL a) :'b word``] th,
                   subst [``x :'a word`` |-> ``n2w (NUMERAL a) :'a word``,
                          ``y :'b word`` |-> ``n2w (NUMERAL a) :'b word``] th])
  [
   ``(x :'a word) < y``,
   ``(x :'a word) <= y``,
   ``word_join (x :'a word) (y :'b word)``,
   ``word_concat (x :'a word) (y :'b word) : 'c word``
  ]);

val WORD_GROUND_ss = simpLib.merge_ss (rewrites alpha_rws ::
  map (fn p => simpLib.conv_ss
    {conv = K (K (CHANGED_CONV WORD_GROUND_CONV)), trace = 3,
     name = "WORD_GROUND_CONV", key = SOME([], p)}) pats);

fun bit_set_compset () =
  let val cmp = words_compset()
      val _ = computeLib.add_thms
                [REWRITE_RULE [GSYM arithmeticTheory.DIV2_def] BIT_SET_def] cmp
  in
    cmp
  end;

val BIT_SET_CONV =
  REWR_CONV BIT_SET
    THENC RAND_CONV (computeLib.CBV_CONV (bit_set_compset()))
    THENC REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY,
            ISPEC `0` pred_setTheory.IN_INSERT,
            ISPEC `NUMERAL n` pred_setTheory.IN_INSERT];

val BIT_ss =
  simpLib.merge_ss [rewrites [BIT_ZERO],
    simpLib.conv_ss
      {conv = K (K (BIT_SET_CONV)), trace = 3,
       name = "BITS_CONV", key = SOME ([], ``BIT b (NUMERAL n)``)}];

val BIT2_ss =
  simpLib.merge_ss [rewrites [BIT_ZERO],
    simpLib.conv_ss
      {conv = K (K (BIT_SET_CONV)), trace = 3,
       name = "BITS_CONV", key = SOME ([], ``BIT 0 (NUMERAL n)``)},
    simpLib.conv_ss
      {conv = K (K (BIT_SET_CONV)), trace = 3,
       name = "BITS_CONV", key = SOME ([], ``BIT (NUMERAL b) (NUMERAL n)``)}];

val WORD_ORDER_ss = rewrites
  [WORD_HIGHER, WORD_HIGHER_EQ,
   WORD_GREATER, WORD_GREATER_EQ,
   WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL,
   WORD_NOT_LESS, WORD_NOT_LESS_EQUAL,
   WORD_LOWER_REFL, WORD_LOWER_EQ_REFL,
   WORD_LESS_REFL, WORD_LESS_EQ_REFL,
   word_T_not_zero, WORD_LS_word_T, WORD_LO_word_T,
   WORD_0_LS, WORD_LESS_0_word_T, WORD_L_LESS_EQ,
   WORD_LS_word_0, WORD_LO_word_0];

(* ------------------------------------------------------------------------- *)

val ADD1 = arithmeticTheory.ADD1;

val WORD_LSL_NUMERAL = (GEN_ALL o SPECL [`a`,`NUMERAL n`]) WORD_MUL_LSL;

val WORD_NOT_NUMERAL =
  (SIMP_RULE std_ss [GSYM ADD1, WORD_LITERAL_ADD, word_sub_def] o
   SPEC `n2w a`) WORD_NOT;

val WORD_NOT_NEG_NUMERAL =
  (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV o GEN_ALL o
   SIMP_RULE arith_ss
     [GSYM ADD1, WORD_LITERAL_ADD, word_sub_def, WORD_NEG_NEG] o
   SPEC `$- (n2w (SUC a))`) WORD_NOT;

val WORD_NOT_NEG_0 = SIMP_CONV std_ss [SYM WORD_NEG_1, WORD_NOT_0, WORD_NEG_0]
  ``~($- 0w) : 'a word``;

val WORD_LITERAL_MULT_thms =
  [word_mul_n2w, WORD_LITERAL_MULT, word_L_MULT, word_L_MULT_NEG,
   GSYM word_L2_def, word_L2_MULT,
   (ONCE_REWRITE_RULE [WORD_MULT_COMM] o CONJUNCT1) WORD_LITERAL_MULT] @
  (map (ONCE_REWRITE_RULE [WORD_MULT_COMM])
     [word_L_MULT, word_L_MULT_NEG, word_L2_MULT]);

val WORD_LITERAL_ADD_thms =
  [word_add_n2w, WORD_LITERAL_ADD,
   (ONCE_REWRITE_RULE [WORD_ADD_COMM] o CONJUNCT2) WORD_LITERAL_ADD];

val word_mult_clauses =
  List.take((map GEN_ALL o CONJUNCTS o SPEC_ALL) WORD_MULT_CLAUSES, 4);

val WORD_MULT_LEFT_1 = List.nth(word_mult_clauses,2);

(* ------------------------------------------------------------------------- *)

fun WORD_LITERAL_REDUCE_CONV t =
  if is_known_word_size t then
    (PURE_ONCE_REWRITE_CONV [GSYM n2w_mod]
       THENC DEPTH_CONV SIZES_CONV
       THENC numLib.REDUCE_CONV
       THENC UINT_MAX_CONV) t
  else
    numLib.REDUCE_CONV t;

fun is_word_literal t =
  if wordsSyntax.is_word_2comp t then
    wordsSyntax.is_word_literal (wordsSyntax.dest_word_2comp t)
  else
    wordsSyntax.is_word_literal t;

(*---------------------------------------------------------------------------*)
(* Tell the function definition mechanism about words.                       *)
(*---------------------------------------------------------------------------*)

val _ =
 let val others = !Literal.other_literals
 in Literal.other_literals := (fn x => others x orelse is_word_literal x)
 end;;


fun is_word_zero t =
  wordsSyntax.is_n2w t andalso
  numLib.dest_numeral (fst (wordsSyntax.dest_n2w t)) = Arbnum.zero;

fun is_word_one t =
  wordsSyntax.is_n2w t andalso
  term_eq ``1n`` (fst(wordsSyntax.dest_n2w t));

val gci_word_mul = GenPolyCanon.GCI
    {dest = wordsSyntax.dest_word_mul,
     is_literal = fn t => is_word_literal t orelse
                          wordsSyntax.is_word_L t orelse
                          wordsSyntax.is_word_L2 t,
     assoc_mode = GenPolyCanon.L_Cflipped,
     assoc = WORD_MULT_ASSOC,
     symassoc = GSYM WORD_MULT_ASSOC,
     comm = WORD_MULT_COMM,
     l_asscomm = GenPolyCanon.derive_l_asscomm WORD_MULT_ASSOC WORD_MULT_COMM,
     r_asscomm = GenPolyCanon.derive_r_asscomm WORD_MULT_ASSOC WORD_MULT_COMM,
     non_coeff = I,
     merge = PURE_REWRITE_CONV WORD_LITERAL_MULT_thms
               THENC WORD_LITERAL_REDUCE_CONV,
     postnorm = REWRITE_CONV (List.take(word_mult_clauses,2)),
     left_id = WORD_MULT_LEFT_1,
     right_id = List.nth(word_mult_clauses,3),
     reducer = PURE_REWRITE_CONV WORD_LITERAL_MULT_thms
                 THENC WORD_LITERAL_REDUCE_CONV};

local
  fun is_good t = let
    val (l,r) = wordsSyntax.dest_word_mul t
  in
    is_word_literal l
  end handle HOL_ERR _ => false
  fun non_coeff t = if is_good t then rand t
                    else if is_word_literal t then mk_var("   ", type_of t)
                    else t
  fun add_coeff (t:term) : thm = if is_good t then ALL_CONV t
                    else REWR_CONV (GSYM WORD_MULT_LEFT_1) t
  val distrib = GSYM WORD_RIGHT_ADD_DISTRIB
  val WORD_REDUCE_CONV = PURE_REWRITE_CONV WORD_LITERAL_ADD_thms
                           THENC WORD_LITERAL_REDUCE_CONV
  fun merge t = let
    val (l,r) = wordsSyntax.dest_word_add t
  in
    if is_word_literal l andalso is_word_literal r then
      WORD_REDUCE_CONV
    else
      Conv.BINOP_CONV add_coeff THENC
      REWR_CONV distrib THENC LAND_CONV WORD_REDUCE_CONV
  end t
in
  val gci_word_add = GenPolyCanon.GCI
    {dest = wordsSyntax.dest_word_add,
     is_literal = is_word_literal,
     assoc_mode = GenPolyCanon.L,
     assoc = WORD_ADD_ASSOC,
     symassoc = GSYM WORD_ADD_ASSOC,
     comm = WORD_ADD_COMM,
     l_asscomm = GenPolyCanon.derive_l_asscomm WORD_ADD_ASSOC WORD_ADD_COMM,
     r_asscomm = GenPolyCanon.derive_r_asscomm WORD_ADD_ASSOC WORD_ADD_COMM,
     non_coeff = non_coeff,
     merge = merge,
     postnorm = REWRITE_CONV word_mult_clauses,
     left_id = CONJUNCT2 WORD_ADD_0,
     right_id = CONJUNCT1 WORD_ADD_0,
     reducer = WORD_REDUCE_CONV}
end;

local
  val conv = PURE_REWRITE_CONV
                 [INT_MAX_def, word_L_def, word_H_def,
                  GSYM WORD_NEG_1, w2n_n2w]
               THENC DEPTH_CONV SIZES_CONV
               THENC numLib.REDUCE_CONV
in
  fun WORD_CONST_CONV t =
    if is_known_word_size t andalso
       (wordsSyntax.is_word_L t orelse
        wordsSyntax.is_word_H t orelse
        wordsSyntax.is_word_T t)
    then
      conv t
    else
      CHANGED_CONV (PURE_REWRITE_CONV [WORD_H_WORD_L, GSYM WORD_NEG_1]) t

  fun WORD_UINT_MAX_CONV t =
    if is_known_word_size t then
      (CHANGED_CONV
        (PURE_REWRITE_CONV [UINT_MAX_def, word_T_def, WORD_NEG_1, w2n_n2w]
         THENC DEPTH_CONV SIZES_CONV
         THENC numLib.REDUCE_CONV)) t
    else
      failwith "Not UINT_MAXw of known size"

  fun WORD_w2n_CONV t =
  let val x = wordsSyntax.dest_w2n t in
    if wordsSyntax.is_n2w x then
      if is_known_word_size x then
        conv t
      else
        CHANGED_CONV (PURE_REWRITE_CONV [word_0_n2w, word_1_n2w]) t
    else
      failwith "Not w2n of word literal"
  end
end;

fun WORD_NEG_CONV t =
let val x = wordsSyntax.dest_word_2comp t in
  if wordsSyntax.is_n2w x then
    if is_known_word_size t andalso not (is_word_one x) then
      (REWR_CONV word_2comp_n2w
        THENC REWR_CONV (GSYM n2w_mod)
        THENC DEPTH_CONV SIZES_CONV THENC numLib.REDUCE_CONV) t
    else
      if is_word_zero x then
        REWR_CONV WORD_NEG_0 t
      else
        failwith "Negative 'a word literal"
  else
    (PURE_REWRITE_CONV [WORD_NEG_L]
       THENC PURE_ONCE_REWRITE_CONV [WORD_NEG_MUL]) t
end;

fun WORD_EQ_CONV t =
let val (x,y) = dest_eq t in
  if wordsSyntax.is_word_type (type_of y) then
    if is_known_word_size x andalso
       wordsSyntax.is_n2w x andalso
       wordsSyntax.is_n2w y
    then
      (PURE_ONCE_REWRITE_CONV [n2w_11]
        THENC DEPTH_CONV SIZES_CONV
        THENC numLib.REDUCE_CONV) t
    else
      if is_word_zero y then
        failwith "RHS is zero"
      else
        PURE_ONCE_REWRITE_CONV [GSYM WORD_EQ_SUB_ZERO] t
  else
    failwith "Not word equality"
end;

fun is_neg_term t =
  wordsSyntax.is_word_2comp t
  orelse
    if wordsSyntax.is_n2w t then
      is_known_word_size t andalso
      let
        val typ = wordsSyntax.dest_word_type (type_of t)
        val tm = wordsSyntax.mk_word_ls (wordsSyntax.mk_word_L typ, t)
      in
        can EQT_ELIM (WORD_EVAL_CONV tm)
      end
    else if  wordsSyntax.is_word_add t then
      is_neg_term (fst (wordsSyntax.dest_word_add t))
    else
      wordsSyntax.is_word_mul t andalso
      is_neg_term (fst (wordsSyntax.dest_word_mul t));

fun FIX_SIGN_OF_NEG_TERM_CONV t =
let val (x,y) = dest_eq t in
   if is_word_zero y andalso is_neg_term x then
     REWR_CONV (GSYM WORD_NEG_EQ_0) t
   else
     failwith "Not neg term with zero RHS"
end;

fun WORD_MULT_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_mul t
   else
     failwith "This convertion can only be applied to word terms";

fun WORD_ADD_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_add t
   else
     failwith "This convertion can only be applied to word terms";

val WORD_MULT_ss = simpLib.merge_ss [rewrites word_mult_clauses,
  simpLib.conv_ss
    {conv = K (K (CHANGED_CONV WORD_MULT_CANON_CONV)), trace = 3,
     name = "WORD_MULT_CANON_CONV", key = SOME([], ``a * b:'a word``)}];

val WORD_ADD_ss = simpLib.conv_ss
  {conv = K (K (CHANGED_CONV WORD_ADD_CANON_CONV)), trace = 3,
   name = "WORD_ADD_CANON_CONV", key = SOME([], ``a + b:'a word``)};

val WORD_SUB_ss = simpLib.merge_ss [rewrites [word_sub_def],
  simpLib.conv_ss
    {conv = K (K (WORD_NEG_CONV)), trace = 3,
     name = "WORD_NEG_CONV", key = SOME([], ``$- a:'a word``)},
  simpLib.conv_ss
    {conv = K (K (WORD_NEG_CONV)), trace = 3,
     name = "WORD_NEG_CONV", key = SOME([], ``a - b:'a word``)}];

val WORD_w2n_ss =
  simpLib.conv_ss
    {conv = K (K (WORD_w2n_CONV)), trace = 3,
     name = "WORD_w2n_CONV", key = SOME([], ``w2n (n2w n :'a word)``)};

val WORD_UINT_MAX_ss = simpLib.merge_ss [
  simpLib.conv_ss
    {conv = K (K (WORD_UINT_MAX_CONV)), trace = 3,
     name = "WORD_UINT_MAX_CONV", key = SOME([], ``$- 1w :'a word``)},
  simpLib.conv_ss
    {conv = K (K (WORD_UINT_MAX_CONV)), trace = 3,
     name = "WORD_UINT_MAX_CONV", key = SOME([], ``UNINT_MAXw :'a word``)}];

val WORD_CONST_ss = simpLib.merge_ss [
  simpLib.conv_ss
    {conv = K (K (WORD_CONST_CONV)), trace = 3,
     name = "WORD_CONST_CONV", key = SOME([], ``INT_MINw:'a word``)},
  simpLib.conv_ss
    {conv = K (K (WORD_CONST_CONV)), trace = 3,
     name = "WORD_CONST_CONV", key = SOME([], ``INT_MAXw:'a word``)},
  simpLib.conv_ss
    {conv = K (K (WORD_CONST_CONV)), trace = 3,
     name = "WORD_CONST_CONV", key = SOME([], ``UINT_MAXw:'a word``)}];

val WORD_ARITH_EQ_ss = simpLib.merge_ss
 [rewrites [WORD_LEFT_ADD_DISTRIB,WORD_RIGHT_ADD_DISTRIB,
            WORD_LSL_NUMERAL,WORD_NOT,hd (CONJUNCTS SHIFT_ZERO)],
  simpLib.conv_ss
    {conv = K (K (WORD_EQ_CONV)), trace = 3,
     name = "WORD_EQ_CONV", key = SOME([], ``a = b:'a word``)}];

val WORD_ARITH_ss =
  simpLib.merge_ss
    [WORD_MULT_ss, WORD_ADD_ss, WORD_SUB_ss, WORD_w2n_ss, WORD_CONST_ss];

val WORD_MULT_CONV = SIMP_CONV (pure_ss++WORD_MULT_ss) [];
val WORD_ADD_CONV = SIMP_CONV (pure_ss++WORD_ADD_ss) [];
val WORD_SUB_CONV = SIMP_CONV (pure_ss++WORD_SUB_ss) [];

local
 val conv = SIMP_CONV (std_ss++WORD_ARITH_EQ_ss++WORD_ARITH_ss) []
in
  val WORD_ARITH_CONV =
     conv THENC (ONCE_DEPTH_CONV FIX_SIGN_OF_NEG_TERM_CONV) THENC conv
end;

(* ------------------------------------------------------------------------- *)

fun bitwise_compset () =
  let open numeral_bitTheory
      val cmp = reduceLib.num_compset()
      val _ = computeLib.add_thms
                [NUMERAL_BITWISE, iBITWISE, numeral_log2,numeral_ilog2] cmp
      val _ = computeLib.add_conv
                (``dimindex:'a itself->num``, 1, SIZES_CONV) cmp
  in
    cmp
  end;

val WORD_LITERAL_AND_thms =
  (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV o
   REWRITE_RULE [WORD_NOT_NUMERAL]) WORD_LITERAL_AND;

val WORD_LITERAL_OR_thms =
  (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV o
   REWRITE_RULE [WORD_NOT_NUMERAL]) WORD_LITERAL_OR;

val BITWISE_CONV = computeLib.CBV_CONV (bitwise_compset ());

val GSYM_WORD_OR_ASSOC = GSYM WORD_OR_ASSOC;
val GSYM_WORD_AND_ASSOC = GSYM WORD_AND_ASSOC;

val WORD_OR_CLAUSES2 = REWRITE_RULE [SYM WORD_NEG_1] WORD_OR_CLAUSES;
val WORD_AND_CLAUSES2 = REWRITE_RULE [SYM WORD_NEG_1] WORD_AND_CLAUSES;

val word_or_clauses = CONJUNCTS (SPEC `a` WORD_OR_CLAUSES2);
val word_and_clauses = CONJUNCTS (SPEC `a` WORD_AND_CLAUSES2);

val WORD_AND_LEFT_T = hd word_and_clauses;

local
  val WORD_REDUCE_CONV =
        PURE_REWRITE_CONV [WORD_AND_CLAUSES2, WORD_LITERAL_AND_thms]
          THENC BITWISE_CONV
          THENC WORD_LITERAL_REDUCE_CONV
in
  val gci_word_and = GenPolyCanon.GCI
   {dest = wordsSyntax.dest_word_and,
    is_literal = is_word_literal,
    assoc_mode = GenPolyCanon.L_Cflipped,
    assoc = GSYM_WORD_AND_ASSOC,
    symassoc = WORD_AND_ASSOC,
    comm = WORD_AND_COMM,
    l_asscomm = GenPolyCanon.derive_l_asscomm GSYM_WORD_AND_ASSOC WORD_AND_COMM,
    r_asscomm = GenPolyCanon.derive_r_asscomm GSYM_WORD_AND_ASSOC WORD_AND_COMM,
    non_coeff = I,
    merge = WORD_REDUCE_CONV,
    postnorm = REWRITE_CONV [WORD_AND_CLAUSES2],
    left_id = WORD_AND_LEFT_T,
    right_id = hd (tl word_and_clauses),
    reducer = WORD_REDUCE_CONV}
end;

local
  fun is_good t = let
    val (l,r) = wordsSyntax.dest_word_and t
  in
    is_word_literal l
  end handle HOL_ERR _ => false
  fun non_coeff t = if is_good t then rand t
                    else if is_word_literal t then
                      mk_var("   ", type_of t)
                    else t
  fun add_coeff (t:term) : thm = if is_good t then ALL_CONV t
                    else REWR_CONV (GSYM WORD_AND_LEFT_T) t
  val distrib = GSYM WORD_RIGHT_AND_OVER_OR
  val WORD_REDUCE_CONV =
         PURE_REWRITE_CONV [WORD_OR_CLAUSES2, WORD_LITERAL_OR_thms]
           THENC BITWISE_CONV
           THENC WORD_LITERAL_REDUCE_CONV
  fun merge t = let
    val (l,r) = wordsSyntax.dest_word_or t
  in
    if is_word_literal l andalso is_word_literal r then
      WORD_REDUCE_CONV
    else
      Conv.BINOP_CONV add_coeff THENC
      REWR_CONV distrib THENC LAND_CONV WORD_REDUCE_CONV
  end t
in
  val gci_word_or = GenPolyCanon.GCI
   {dest = wordsSyntax.dest_word_or,
    is_literal = is_word_literal,
    assoc_mode = GenPolyCanon.L,
    assoc = GSYM_WORD_OR_ASSOC,
    symassoc = WORD_OR_ASSOC,
    comm = WORD_OR_COMM,
    l_asscomm = GenPolyCanon.derive_l_asscomm GSYM_WORD_OR_ASSOC WORD_OR_COMM,
    r_asscomm = GenPolyCanon.derive_r_asscomm GSYM_WORD_OR_ASSOC WORD_OR_COMM,
    non_coeff = non_coeff,
    merge = merge,
    postnorm = PURE_REWRITE_CONV [WORD_OR_CLAUSES2],
    left_id = hd word_or_clauses,
    right_id = hd (tl word_or_clauses),
    reducer = WORD_REDUCE_CONV}
end;

fun WORD_COMP_CONV t =
let val x = wordsSyntax.dest_word_1comp t in
  if is_known_word_size t then
    if is_word_zero x then
      PURE_REWRITE_CONV [REWRITE_RULE [SYM WORD_NEG_1] WORD_NOT_0] t
    else
      (PURE_REWRITE_CONV [word_1comp_n2w]
        THENC DEPTH_CONV SIZES_CONV THENC numLib.REDUCE_CONV) t
  else
    (PURE_REWRITE_CONV [WORD_NOT_NUMERAL]
      THENC numLib.REDUCE_CONV) t
end;

fun WORD_AND_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_and t
   else
     failwith "This convertion can only be applied to word terms";

fun WORD_OR_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_or t
   else
     failwith "This convertion can only be applied to word terms";

val WORD_COMP_ss =
  simpLib.merge_ss [
    rewrites [WORD_DE_MORGAN_THM, WORD_NOT_NOT,
              WORD_NOT_NEG_NUMERAL, WORD_NOT_NEG_0],
    simpLib.conv_ss
      {conv = K (K (WORD_COMP_CONV)), trace = 3,
       name = "WORD_COMP_CONV", key = SOME ([], ``~(n2w a) :'a word``)}];

val WORD_AND_ss =
  simpLib.merge_ss [rewrites [WORD_AND_CLAUSES2, SYM WORD_NEG_1, WORD_AND_COMP],
  simpLib.conv_ss
    {conv = K (K (WORD_AND_CANON_CONV)), trace = 3,
     name = "WORD_AND_CANON_CONV", key = SOME ([], ``a && b:'a word``)}];

val WORD_OR_ss = let val thm = REWRITE_RULE [SYM WORD_NEG_1] WORD_OR_COMP in
  simpLib.merge_ss
  [rewrites [WORD_OR_CLAUSES2, SYM WORD_NEG_1, WORD_AND_ABSORD, thm,
   ONCE_REWRITE_RULE [WORD_OR_COMM] thm],
   simpLib.conv_ss
     {conv = K (K (WORD_OR_CANON_CONV)), trace = 3,
      name = "WORD_OR_CANON_CONV", key = SOME ([], ``a !! b:'a word``)}]
end;

val WORD_LOGIC_ss = simpLib.merge_ss [WORD_COMP_ss,WORD_AND_ss,WORD_OR_ss];

val WORD_COMP_CONV = SIMP_CONV (pure_ss++WORD_COMP_ss) [];
val WORD_AND_CONV = SIMP_CONV (pure_ss++WORD_AND_ss) [];
val WORD_OR_CONV = SIMP_CONV (pure_ss++WORD_OR_ss) [];

val WORD_LOGIC_CONV = SIMP_CONV (bool_ss++WORD_LOGIC_ss)
  [WORD_LEFT_AND_OVER_OR,WORD_RIGHT_AND_OVER_OR,WORD_XOR,REFL_CLAUSE];

(* ------------------------------------------------------------------------- *)

val ROL_ROR_MOD_RWT = prove(
  ``!n w:'a word. dimindex (:'a) <= n ==>
                 (w #<< n = w #<< (n MOD dimindex (:'a))) /\
                 (w #>> n = w #>> (n MOD dimindex (:'a)))``,
  SRW_TAC [] [Once (GSYM ROL_MOD), Once (GSYM ROR_MOD)]);

val WORD_SHIFT_ss =
  rewrites
    ([SHIFT_ZERO, ZERO_SHIFT, word_rrx_0, word_rrx_word_T, lsr_1_word_T,
      LSL_ADD, LSR_ADD, ASR_ADD, ROR_ROL, ROR_ADD, ROL_ADD, ROL_ROR_MOD_RWT,
      WORD_ADD_LSL, GSYM WORD_2COMP_LSL,
      GSYM LSL_BITWISE, GSYM LSR_BITWISE, GSYM ROR_BITWISE, GSYM ROL_BITWISE,
      LSL_LIMIT, LSR_LIMIT, ASR_LIMIT] @
    map (REWRITE_RULE [SYM WORD_NEG_1])
     [ASR_UINT_MAX, ROR_UINT_MAX,
      (REWRITE_RULE [ROR_UINT_MAX] o SPEC `UINT_MAXw`) word_rol_def]);

(* ------------------------------------------------------------------------- *)

local
  fun odd n = Arbnum.mod2 n = Arbnum.one
  fun num2list' i l n =
        if n = Arbnum.zero then
          l
        else
          num2list' (Arbnum.plus1 i) (if odd n then i::l else l) (Arbnum.div2 n)
  val num2list = num2list' Arbnum.zero []
in
  val word2list = num2list o numSyntax.dest_numeral o fst o wordsSyntax.dest_n2w
end;

fun shift_n t n =
   if n = Arbnum.zero then
     t
   else
     wordsSyntax.mk_word_lsl(t, numSyntax.mk_numeral n);

fun sum_n l = foldl (fn (a,b) => wordsSyntax.mk_word_add(b,a)) (hd l) (tl l);

fun WORD_MUL_LSL_CONV t =
let val (l,r) = wordsSyntax.dest_word_mul t in
  if wordsSyntax.is_n2w l andalso not (wordsSyntax.is_word_literal r) then
    let val t' = sum_n (map (shift_n r) (word2list l))
        val thm = SIMP_CONV (std_ss++WORD_ARITH_ss) [WORD_MUL_LSL] (mk_eq(t,t'))
    in
      EQT_ELIM thm
    end
  else
    failwith "Not a term of the form: n2w n * x."
end;

val WORD_MUL_LSL_ss =
  simpLib.conv_ss
    {conv = K (K (WORD_MUL_LSL_CONV)), trace = 3, name = "WORD_MUL_LSL_CONV",
     key = SOME([], ``n2w (NUMERAL n) * a:'a word``)};

(* ------------------------------------------------------------------------- *)

val LET_RULE = SIMP_RULE (bool_ss++boolSimps.LET_ss) [];
val OR_AND_COMM_RULE = ONCE_REWRITE_RULE [WORD_ADD_COMM, WORD_OR_COMM];

val WORD_EXTRACT_ss =
  rewrites ([WORD_EXTRACT_ZERO, WORD_EXTRACT_ZERO2, WORD_EXTRACT_ZERO3,
      WORD_EXTRACT_LSL, word_concat_def, LET_RULE word_join_def,
      word_rol_def, LET_RULE word_ror, word_asr, word_lsr_n2w,
      WORD_EXTRACT_COMP_THM, WORD_EXTRACT_MIN_HIGH,
      EXTRACT_JOIN, EXTRACT_JOIN_LSL,
      EXTRACT_JOIN_ADD, EXTRACT_JOIN_ADD_LSL,
      OR_AND_COMM_RULE EXTRACT_JOIN, OR_AND_COMM_RULE EXTRACT_JOIN_LSL,
      OR_AND_COMM_RULE EXTRACT_JOIN_ADD, OR_AND_COMM_RULE EXTRACT_JOIN_ADD_LSL,
      GSYM WORD_EXTRACT_OVER_BITWISE,
      (GEN_ALL o ISPEC `(h >< l):'a word -> 'b word`) COND_RAND,
      WORD_BITS_EXTRACT, WORD_w2w_EXTRACT, sw2sw_w2w, word_lsb, word_msb] @
    map (REWRITE_RULE [WORD_BITS_EXTRACT])
     [WORD_ALL_BITS, WORD_SLICE_THM, WORD_BIT_BITS]);

(* ------------------------------------------------------------------------- *)

val WORD_ss =
  simpLib.merge_ss [WORD_LOGIC_ss, WORD_ARITH_ss, WORD_SHIFT_ss,
    WORD_GROUND_ss, BIT_ss, SIZES_ss];

val WORD_CONV = SIMP_CONV (std_ss++WORD_ss)
  [WORD_LEFT_ADD_DISTRIB, WORD_RIGHT_ADD_DISTRIB,
   WORD_LEFT_AND_OVER_OR, WORD_RIGHT_AND_OVER_OR, WORD_XOR];

val _ = augment_srw_ss [WORD_ss];

(* ------------------------------------------------------------------------- *)

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val LESS_COR = REWRITE_RULE [DISJ_IMP_THM] (CONJ
  ((GEN_ALL o REWRITE_CONV [LESS_THM]) ``m < NUMERAL (BIT1 n) ==> p``)
  ((GEN_ALL o REWRITE_CONV [LESS_THM]) ``m < NUMERAL (BIT2 n) ==> p``));

local
  fun w2n_of_known_size t =
    let val x = wordsSyntax.dest_w2n t in
      (is_known_word_size x andalso not (wordsSyntax.is_word_literal x))
    end handle HOL_ERR _ => false

  fun removeDuplicates l = let open Binaryset in
     listItems (addList (empty compare, l))
  end

  fun mk_bounds_thm t =
    let val x = wordsSyntax.dest_w2n t in
      if is_known_word_size x then
        (CONV_RULE (DEPTH_CONV SIZES_CONV) o Drule.ISPEC x) w2n_lt
      else
        failwith "Unknown size"
    end
in
  fun mk_bounds_thms t =
  let val l = removeDuplicates (find_terms w2n_of_known_size t)
  in
    if null l then
      TRUTH
    else
      LIST_CONJ (map mk_bounds_thm l)
  end
end;

val EXISTS_NUMBER = prove(
  ``(?w:'a word. P (w2n w)) = (?n. n < dimword(:'a) /\ P n)``,
  EQ_TAC THEN SRW_TAC [] []
    THENL [Q.EXISTS_TAC `w2n w`, Q.EXISTS_TAC `n2w n`]
    THEN ASM_SIMP_TAC std_ss [w2n_lt, w2n_n2w]);

fun EXISTS_WORD_CONV t =
  if is_exists t then
    let val v = fst (dest_exists t) in
      if wordsSyntax.is_word_type (type_of v) then
        (UNBETA_CONV v THENC SIMP_CONV (std_ss++SIZES_ss) [EXISTS_NUMBER]) t
      else
        failwith "Not an \"exists word\" term."
    end
  else
    failwith "Not an exists term.";

local
  val word_join = SIMP_RULE (std_ss++boolSimps.LET_ss) [] word_join_def
  val rw1 = [word_0,word_T,word_L,word_xor_def,word_or_def,word_and_def,
             word_1comp_def, REWRITE_RULE [SYM WORD_NEG_1] word_T,
             SPEC `NUMERAL n` n2w_def,
             pred_setTheory.NOT_IN_EMPTY,
             ISPEC `0` pred_setTheory.IN_INSERT,
             ISPEC `NUMERAL n` pred_setTheory.IN_INSERT]
  val rw2 = [fcpTheory.FCP_UPDATE_def,LESS_COR,sw2sw,w2w,
             word_join,word_concat_def,word_reverse_def,word_modify_def,
             word_lsl_def,word_lsr_def,word_asr_def,word_ror_def,
             word_rol_def,word_rrx_def,word_msb_def,word_lsb_def,
             word_extract_def,word_bits_def,word_slice_def,word_bit_def]
  val thms = [WORD_ADD_LEFT_LO, WORD_ADD_LEFT_LS,
              WORD_ADD_RIGHT_LS, WORD_ADD_RIGHT_LO]
  val thms2 = map (GEN_ALL o SPEC `n2w n`)
               [WORD_ADD_LEFT_LO2, WORD_ADD_LEFT_LS2,
                WORD_ADD_RIGHT_LO2, WORD_ADD_RIGHT_LS2]
  val rw3 = [WORD_LT_LO, WORD_LE_LS, WORD_GREATER, WORD_GREATER_EQ,
             CONV_RULE WORD_ARITH_CONV WORD_LS_T,
             CONV_RULE WORD_ARITH_CONV WORD_LESS_EQ_H] @
             map (SPECL [`n2w m`, `n2w n`]) thms @
             thms2 @ map (ONCE_REWRITE_RULE [WORD_ADD_COMM]) thms2
  val rw4 = [SPECL [`w`,`n2w m`, `n2w n`] WORD_ADD_EQ_SUB,
             SPECL [`w`,`$- (n2w m)`, `n2w n`] WORD_ADD_EQ_SUB,
             REWRITE_RULE [GSYM w2n_11, word_0_n2w] NOT_INT_MIN_ZERO,
             REWRITE_RULE [WORD_LO, word_0_n2w] ZERO_LO_INT_MIN,
             WORD_LO, WORD_LS, WORD_HI, WORD_HS, GSYM w2n_11]
  val DECIDE_CONV = EQT_INTRO o DECIDE
  fun EQ_CONV t = (if term_eq T t orelse term_eq F t then
                     ALL_CONV else NO_CONV) t
in
  fun WORD_BIT_EQ_CONV t =
        if is_eq t orelse wordsSyntax.is_index t then
          ((SIMP_CONV (std_ss++fcpLib.FCP_ss++BIT_ss) rw1
             THENC TRY_CONV DECIDE_CONV
             THENC SIMP_CONV (arith_ss++fcpLib.FCP_ss++SIZES_ss++
                     BIT_ss) (rw1 @ rw2)
             THENC REDEPTH_CONV FORALL_AND_CONV
             THENC SIMP_CONV arith_ss []) t)
        else
          failwith "Not a word equality"
  val WORD_BIT_EQ_ss =
        simpLib.merge_ss [ARITH_ss, fcpLib.FCP_ss, SIZES_ss, BIT2_ss,
          rewrites rw1, rewrites rw2,
          simpLib.conv_ss
            {conv = K (K (CHANGED_CONV FORALL_AND_CONV)), trace = 3,
             name = "FORALL_AND_CONV",
             key = SOME([], ``!x:'a. P /\ Q``)}]
  fun WORD_DP_PROVE dp t =
        let val thm1 = QCONV (
                        WORD_CONV
                          THENC SIMP_CONV (bool_ss++WORD_CONST_ss++
                                 WORD_UINT_MAX_ss) rw3
                          THENC SIMP_CONV (std_ss++boolSimps.LET_ss++
                                 WORD_UINT_MAX_ss++WORD_w2n_ss++WORD_SUB_ss++
                                 WORD_ADD_ss) rw4
                          THENC DEPTH_CONV EXISTS_WORD_CONV) t
            val t1 = rhs (concl thm1)
            val bnds = mk_bounds_thms t1
            val t2 = mk_imp (concl bnds, t1)
            val thm2 = dp t2
            val conv = RAND_CONV (PURE_ONCE_REWRITE_CONV [GSYM thm1])
        in
          MP (CONV_RULE conv thm2) bnds
        end
   fun WORD_DP dp tm =
          let fun conv t =
                if term_eq T t then
                  ALL_CONV t
                else if is_forall t then
                  STRIP_QUANT_CONV (EQT_INTRO o (WORD_DP_PROVE dp)) t
                else
                  (EQT_INTRO o WORD_DP_PROVE dp) t
          in
            EQT_ELIM
              ((WORD_CONV THENC DEPTH_CONV (WORD_BIT_EQ_CONV THENC EQ_CONV)
                 THENC DEPTH_CONV (conv THENC EQ_CONV)
                 THENC REWRITE_CONV []) tm)
          end
   val WORD_DECIDE = WORD_DP DECIDE
end;

fun is_word_term tm = let open numSyntax in
  if is_forall tm then
    is_word_term (#Body (Rsyntax.dest_forall tm))
  else if is_exists tm then
    is_word_term (#Body (Rsyntax.dest_exists tm))
  else if is_neg tm then
    is_word_term (dest_neg tm)
  else if is_conj tm orelse is_disj tm orelse is_imp tm then
    is_word_term (rand (rator tm)) andalso is_word_term (rand tm)
  else if is_eq tm then
    let val typ = type_of (rand tm) in
      (typ = num) orelse is_word_type typ
    end
  else
    is_less tm orelse is_leq tm orelse is_greater tm orelse is_geq tm orelse
    is_index tm orelse
    is_word_lt tm orelse is_word_le tm orelse
    is_word_gt tm orelse is_word_ge tm orelse
    is_word_hi tm orelse is_word_lo tm orelse
    is_word_hs tm orelse is_word_ls tm
end;

fun MP_ASSUM_TAC tm (asl, w) =
  let val (ob, asl') = Lib.pluck (Lib.equal tm) asl in
    MP_TAC (Thm.ASSUME ob) (asl', w)
  end;

fun WORD_DECIDE_TAC (asl, w) =
  (EVERY (map MP_ASSUM_TAC (List.filter is_word_term asl)) THEN
    CONV_TAC (WORD_DP DECIDE)) (asl, w);

(* ------------------------------------------------------------------------- *)

fun mk_word_size n =
  let val N = Arbnum.fromInt n
      val SN = Int.toString n
      val typ = fcpLib.index_type N
      val TYPE = mk_type("cart", [bool, typ])
      val dimindex = fcpLib.DIMINDEX N
      val finite = fcpLib.FINITE N
      val _ = save_thm("dimindex_" ^ SN, dimindex)
      val _ = save_thm("finite_" ^ SN, finite)
      val INT_MIN = save_thm("INT_MIN_" ^ SN,
                     (SIMP_RULE std_ss [dimindex] o
                      Thm.INST_TYPE [``:'a`` |-> typ]) INT_MIN_def)
      val dimword = save_thm("dimword_" ^ SN,
                     (SIMP_RULE std_ss [INT_MIN] o
                      Thm.INST_TYPE [``:'a`` |-> typ]) dimword_IS_TWICE_INT_MIN)
  in
    type_abbrev("word" ^ SN, TYPE)
  end;

(* ------------------------------------------------------------------------- *)

val RHS_REWRITE_RULE =
  GEN_REWRITE_RULE (DEPTH_CONV o RAND_CONV) empty_rewrites;

val WORDS_EMIT_RULE =
  BETA_RULE o PURE_REWRITE_RULE ([BIT_UPDATE, literal_case_THM] @ (map GSYM
    [word_index_def, n2w_itself_def, w2w_itself_def, sw2sw_itself_def,
     word_concat_itself_def, word_extract_itself_def,
     fcpTheory.FCPi_def, fcpTheory.mk_fcp_def, literal_case_DEF])) o
  RHS_REWRITE_RULE [GSYM word_eq_def];

(* ------------------------------------------------------------------------- *)

fun Cases_on_word tm =
   Q.ISPEC_THEN tm FULL_STRUCT_CASES_TAC ranged_word_nchotomy;

fun Cases_word (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_word" "not a forall")
  in (STRIP_TAC THEN STRUCT_CASES_TAC (Drule.ISPEC Bvar ranged_word_nchotomy)) g
  end;

val Induct_word =
  recInduct WORD_INDUCT
    THEN CONJ_TAC
    THENL [ALL_TAC,
      CONV_TAC (QCONV (TRY_CONV (STRIP_QUANT_CONV
                  (RATOR_CONV (DEPTH_CONV SIZES_CONV)))))
        THEN NTAC 3 STRIP_TAC];

(* ------------------------------------------------------------------------- *)

fun print_word f sys gravs d pps t = let
   open Portable term_pp_types
   val (n,x) = dest_n2w t
   val m = fcpLib.index_to_num x handle _ => Arbnum.zero
   val v = numSyntax.dest_numeral n
in
  add_string pps
   ((case f (Arbnum.toInt m, v) of
       StringCvt.DEC => Arbnum.toString v
     | StringCvt.BIN => "0b"^(Arbnum.toBinString v)
     | StringCvt.OCT => if !base_tokens.allow_octal_input orelse
                           Arbnum.<(v, Arbnum.fromInt 8)
                        then
                          "0" ^(Arbnum.toOctString v)
                        else
                          (Feedback.HOL_MESG "Octal output is only supported \
                             \when base_tokens.allow_octal_input is true.";
                           Arbnum.toString v)
     | StringCvt.HEX => "0x"^(Arbnum.toHexString v)) ^ "w")
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun output_words_as f = Parse.temp_add_user_printer
  ({Tyop = "cart", Thy = "fcp"}, print_word f);

fun output_words_as_bin() = output_words_as (K StringCvt.BIN);
fun output_words_as_hex() = output_words_as (K StringCvt.HEX);

fun output_words_as_oct() =
  (base_tokens.allow_octal_input := true; output_words_as (K StringCvt.OCT));

fun output_words_as_dec() =
  (Parse.remove_user_printer {Tyop="cart", Thy="fcp"}; ());

val _ = output_words_as
   (fn (l, v) =>
       if Arbnum.<=(Arbnum.fromHexString "10000", v) then 
         StringCvt.HEX
       else
         StringCvt.DEC);

(* ------------------------------------------------------------------------- *)
(* Guessing the word length for the result of extraction (><) and            *)
(* concatenate (@@)                                                          *)
(* ------------------------------------------------------------------------- *)

val extract_tm = ``(a >< b) :'a word -> 'b word``;

datatype WordOp =
   word_concat of hol_type * hol_type * hol_type
 | word_extract of num * hol_type;

fun get_word_ops t =
  case total (match_term extract_tm) t of
    NONE =>
      (case dest_term t of
         VAR (a, b) => []
       | CONST a =>
           if #Name a = "word_concat" then
            (case dest_type (#Ty a) of
               ("fun", [x,y]) =>
                 (case dest_type y of
                    ("fun", [v,w]) =>
                       (let val fv = hd (type_vars w)
                            val xn = wordsSyntax.dest_word_type x
                            val vn = wordsSyntax.dest_word_type v
                        in
                          [word_concat (xn, vn, fv)]
                        end handle _ => [])
                  | _ => [])
             | _ => [])
           else
             []
       | COMB (a,b) => get_word_ops a @ get_word_ops b
       | LAMB (a,b) => get_word_ops b)
  | SOME ([a,b],_) =>
      (case dest_type (type_of t) of
         ("fun", [x, y]) =>
            (let val fv = hd (type_vars y)
                 val na = numSyntax.dest_numeral (#residue a)
                 val nb = numSyntax.dest_numeral (#residue b)
                 val n = Arbnum.-(Arbnum.plus1 na, nb)
             in
               if n = Arbnum.zero then [] else [word_extract (n, fv)]
             end handle _ => [])
      | _ => [])
  | _ => [];

fun word_op_compare(a, b) =
  case (a, b) of
    (word_concat(a,b,c),word_concat(d,e,f)) =>
       if a = f orelse b = f then
         if d = c orelse e = c then Type.compare(c, f) else GREATER
       else
         if d = c orelse e = c then LESS else Type.compare(c, f)
  | (word_concat(a,b,c),word_extract(n,f))  => GREATER
  | (word_extract(m,c),word_concat(d,e,f))  => LESS
  | (word_extract(m,c),word_extract(n,f))   => Type.compare(c, f);

local
  open Redblackmap

  fun mk_word_op_var_map vmap [] = vmap
    | mk_word_op_var_map vmap (word_extract (n, ty)::tl) =
       (case peek(vmap, ty) of
          NONE   => mk_word_op_var_map (insert(vmap,ty,n)) tl
        | SOME m => mk_word_op_var_map (if Arbnum.<(n, m) then vmap
                                        else insert(vmap,ty,n)) tl)
    | mk_word_op_var_map vmap (word_concat (a, b, ty)::tl) =
       (let val na = if Type.is_vartype a then
                       find(vmap, a)
                     else
                       fcpLib.index_to_num a
            val nb = if Type.is_vartype b then
                       find(vmap, b)
                     else
                       fcpLib.index_to_num b
            val n = Arbnum.+(na, nb)
        in
          case peek(vmap, ty) of
            NONE   => mk_word_op_var_map (insert(vmap,ty,n)) tl
          | SOME m => mk_word_op_var_map (if Arbnum.<(n, m) then vmap
                                          else insert(vmap,ty,n)) tl
        end handle _ => mk_word_op_var_map vmap tl)
in
  fun mk_vmap t = mk_word_op_var_map (mkDict Type.compare)
                    (Listsort.sort word_op_compare (get_word_ops t))
end;

fun word_op_type_inst (ty:hol_type, n) =
  {redex = ty, residue = fcpLib.index_type n};

val notify_word_length_guesses = ref true;

val _ = Feedback.register_btrace("notify word length guesses",
                                  notify_word_length_guesses);

local
  fun comma_separate_acc [] l = l
    | comma_separate_acc (h::t) "" = comma_separate_acc t h
    | comma_separate_acc [h] l = l ^ " and " ^ h
    | comma_separate_acc (h::t) l = comma_separate_acc t (l ^ ", " ^ h)
in
  fun comma_separate l = comma_separate_acc l ""
end;

fun type_name t = String.extract(Hol_pp.type_to_string t, 1, NONE);

fun guess_to_string {redex = a, residue = b} =
  type_name a ^ " <- " ^ type_name b;

fun print_guesses l = Feedback.HOL_MESG
  ("assigning word length(s): " ^ comma_separate (map guess_to_string l));

fun guess_word_lengths t =
let val assigns = map word_op_type_inst (Redblackmap.listItems (mk_vmap t))
    val _ = if !Globals.interactive andalso
               !notify_word_length_guesses andalso
               not (null assigns)
            then
              print_guesses assigns
            else
              ()
in
  inst assigns t
end

val save_post_process_term = !Parse.post_process_term;

fun guess_lengths () = Parse.post_process_term :=
  (guess_word_lengths o fcpLib.guess_fcp_lengths o !Parse.post_process_term);

fun dont_guess_lengths () = Parse.post_process_term := save_post_process_term;

val operators = [("+", ``($+ :bool['a] -> bool['a] -> bool['a])``),
                 ("-", ``($- :bool['a] -> bool['a] -> bool['a])``),
                 ("-", ``($- :bool['a] -> bool['a])``),
                 ("*", ``($* :bool['a] -> bool['a] -> bool['a])``),
                 ("<", ``($< :bool['a] -> bool['a] -> bool)``),
                 ("<=", ``($<= :bool['a] -> bool['a] -> bool)``),
                 (">", ``($> :bool['a] -> bool['a] -> bool)``),
                 (">=", ``($>= :bool['a] -> bool['a] -> bool)``)];

fun deprecate_word () = let
  fun losety {Name,Thy,Ty} = {Name = Name, Thy = Thy}
  fun doit (s, t) = Parse.temp_remove_ovl_mapping s (losety (dest_thy_const t))
in
  app (ignore o doit) operators
end

fun prefer_word () = app temp_overload_on operators

end
