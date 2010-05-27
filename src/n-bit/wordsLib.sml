structure wordsLib :> wordsLib =
struct

(* interactive use:
  app load ["fcpLib", "numeral_bitTheory", "wordsTheory", "wordsSyntax",
            "stringSyntax"];
*)

open HolKernel Parse boolLib bossLib computeLib;
open bitTheory numeral_bitTheory wordsTheory wordsSyntax;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars wordsTheory.words_grammars
end
open Parse

val _ = Lib.with_flag (Feedback.emit_MESG, false) bossLib.srw_ss ()

val ISPEC = Q.ISPEC;
val SPEC  = Q.SPEC;
val SPECL = Q.SPECL;
val INST  = Q.INST;

val ERR = mk_HOL_ERR "wordsLib";

(*---------------------------------------------------------------------------*)
(* Tell the function definition mechanism about words.                       *)
(*---------------------------------------------------------------------------*)

fun is_word_literal t =
  if wordsSyntax.is_word_2comp t then
    wordsSyntax.is_word_literal (wordsSyntax.dest_word_2comp t)
  else
    wordsSyntax.is_word_literal t;

val _ =
 let val others = !Literal.other_literals
 in Literal.other_literals := (fn x => others x orelse is_word_literal x)
 end;

fun is_word_zero t =
  wordsSyntax.is_n2w t andalso
  numLib.dest_numeral (fst (wordsSyntax.dest_n2w t)) = Arbnum.zero;

fun is_word_one t =
  wordsSyntax.is_n2w t andalso
  term_eq ``1n`` (fst(wordsSyntax.dest_n2w t));

fun is_uintmax t =
  wordsSyntax.is_word_2comp t andalso
  is_word_one (wordsSyntax.dest_word_2comp t);

val Na = ``arithmetic$NUMERAL ^(mk_var("a", numLib.num))``;
val n2w = ``words$n2w : num -> 'a word``;

(* ------------------------------------------------------------------------- *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

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
  fun SIZES_CONV t = let
       val exn = ERR "SIZES_CONV"
                     "Term not dimword, dimindex, INT_MIN or FINITE"
       val rtr = Lib.with_exn (fst o dest_const o rator) t exn
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
        raise exn
    end
end;

val SIZES_ss =
  simpLib.named_merge_ss "sizes"
    [simpLib.rewrites [ONE_LT_dimword, DIMINDEX_GT_0],
     simpLib.std_conv_ss
      {name = "SIZES_CONV",
       conv = SIZES_CONV,
       pats = [``fcp$dimindex(:'a)``,
               ``pred_set$FINITE (pred_set$UNIV:'a set)``,
               ``words$INT_MIN(:'a)``,
               ``words$dimword(:'a)``]}];

fun NUM_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ
     ((GEN_ALL o simpLib.SIMP_RULE (bossLib.arith_ss++boolSimps.LET_ss) l o
       INST [n |-> `0n`]) y)
     ((GEN_ALL o INST [n |-> `^Na`]) y)
  end;

val MOD_WL =
  (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))));

val MOD_WL1 =
  (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (RATOR_CONV
   (ONCE_REWRITE_CONV [GSYM n2w_mod])))));

val word_EQ_CONV =
let
 fun is_word_literal t = wordsSyntax.is_word_literal t orelse is_uintmax t
 val comp = reduceLib.num_compset()
 val _ = add_thms
          (word_eq_n2w :: map (SUC_RULE) [MOD_2EXP_EQ, MOD_2EXP_MAX]) comp
 val _ = add_conv(``fcp$dimindex:'a itself -> num``, 1, SIZES_CONV) comp
in
 fn tm =>
   case total dest_eq tm
   of NONE => raise ERR "word_EQ_CONV" "not an equality"
    | SOME(w1,w2) =>
      if is_word_literal w1 andalso is_word_literal w2
      then if w1=w2
           then Thm.SPEC w1 (INST_TYPE[alpha|->type_of w1] REFL_CLAUSE)
           else
                if null (type_vars_in_term w1)
                then CHANGED_CONV (CBV_CONV comp) tm
                else raise ERR "word_EQ_CONV" "contains type variables"
      else raise ERR "word_eq_CONV" "non-literal in equality"
end;

fun l2n_pow2 i =
let open Arbnum numSyntax
    val t = mk_numeral (Arbnum.log2 (Arbnum.fromInt i))
    val (l,r) = CONJ_PAIR l2n_pow2_compute in
  SIMP_RULE std_ss [] (CONJ (Thm.SPEC t l) (Thm.SPEC t r))
end;

fun n2l_pow2 i =
let open Arbnum numSyntax
    val t = mk_numeral (Arbnum.log2 (Arbnum.fromInt i))
in
  SIMP_RULE std_ss [] (Thm.SPEC t n2l_pow2_compute)
end;

val w2n_n2w_compute = prove(
  ``!n. w2n ((n2w n) : 'a word) =
       if n < dimword(:'a) then n else n MOD dimword(:'a)``,
  SRW_TAC [boolSimps.LET_ss] []);

val word_2comp_compute = prove(
  ``!n. word_2comp (n2w n) : 'a word =
        let x = n MOD dimword (:'a) in
          if x = 0 then 0w else n2w (dimword (:'a) - x)``,
  SRW_TAC [boolSimps.LET_ss] [word_2comp_n2w]);

val word_lsr_compute =
  (REWRITE_RULE [word_bits_n2w, arithmeticTheory.MIN_IDEM] o
   SPECL [`^n2w n`,`^Na`]) word_lsr_n2w;

val word_asr_compute =
  (REWRITE_RULE [word_bits_n2w, word_msb_n2w, word_or_n2w,
     word_lsr_compute, arithmeticTheory.MIN_IDEM] o
   SPECL [`^Na`, `^n2w n`]) word_asr_n2w;

val bit_update_compute =
   BIT_UPDATE |> REWRITE_RULE [FUN_EQ_THM]
              |> (fn th => CONJ (SPECL [`^Na`, `F`,`^n2w n`] th)
                                (SPECL [`^Na`, `T`,`^n2w n`] th))

val thms =
  [numeralTheory.numeral_funpow, pairTheory.UNCURRY_DEF,
   SUC_RULE rich_listTheory.GENLIST, rich_listTheory.SNOC, combinTheory.K_THM,
   iBITWISE, NUMERAL_BITWISE, LSB_def, BITV_def, SBIT_def,
   NUM_RULE [BIT_ZERO] `n:num` SIGN_EXTEND_def,
   DIVMOD_2EXP, NUMERAL_DIV_2EXP, NUMERAL_TIMES_2EXP, NUMERAL_iDIV2,
   NUMERAL_SFUNPOW_iDIV2,NUMERAL_SFUNPOW_iDUB,NUMERAL_SFUNPOW_FDUB,
   FDUB_iDIV2,FDUB_iDUB,FDUB_FDUB,
   NUMERAL_BIT_MODIFY, NUMERAL_BIT_MODF,
   NUMERAL_BIT_REVERSE, NUMERAL_BIT_REV,
   NUM_RULE [NUMERAL_DIV_2EXP,numeralTheory.MOD_2EXP] `n:num` BITS_def,
   NUM_RULE [NUMERAL_DIV_2EXP,numeralTheory.MOD_2EXP] `n:num` SLICE_def,
   (SIMP_RULE std_ss [GSYM ODD_MOD2_LEM,arithmeticTheory.MOD_2EXP_def,
      BITS_def,SUC_SUB] o NUM_RULE [BITS_ZERO2] `n:num`) BIT_def,
   UINT_MAX_def, INT_MAX_def, INT_MIN_SUM,
   SUC_RULE MOD_2EXP_EQ, SUC_RULE BOOLIFY_def, bit_update_compute,
   numeral_log2,numeral_ilog2,LOG_compute,LOWEST_SET_BIT_compute,
   n2w_w2n, w2n_n2w_compute, MOD_WL1 w2w_n2w, Q.SPEC `^n2w n` sw2sw_def,
   word_len_def, word_L_def, word_H_def, word_T_def,
   word_join_def, SPECL [`^n2w n`,`n2w m:'b word`] word_concat_def,
   SPEC `^Na` word_replicate_concat_word_list, concat_word_list_def,
   word_reverse_n2w, word_modify_n2w, bit_field_insert_def,
   SPEC `^Na` word_log2_n2w,
   word_1comp_n2w, word_or_n2w, word_xor_n2w, word_and_n2w,
   word_2comp_compute, word_nor_n2w, word_xnor_n2w, word_nand_n2w,
   word_sub_def, word_div_def, word_sdiv_def, word_mod_def,
   MOD_WL word_add_n2w, MOD_WL word_mul_n2w,
   word_asr_compute, word_lsr_compute, SPEC `^Na` word_lsl_n2w,
   SHIFT_ZERO, SPEC `^Na` word_ror_n2w,
   SPECL [`w:'a word`,`^Na`] word_rol_def, word_rrx_n2w,
   word_lsb_n2w, word_msb_n2w, word_bit_n2w, fcp_n2w, fcpTheory.L2V_def,
   NUM_RULE [DIMINDEX_GT_0] `i:num` word_index_n2w,
   NUM_RULE [DIMINDEX_GT_0] `n:num` fcpTheory.index_comp,
   NUM_RULE [DIMINDEX_GT_0] `b:num` fcpTheory.FCP_APPLY_UPDATE_THM,
   word_bits_n2w, word_signed_bits_n2w, word_slice_n2w, word_extract_n2w,
   word_reduce_n2w, Q.SPEC `^n2w n` reduce_and, Q.SPEC `^n2w n` reduce_or,
   reduce_xor_def, reduce_xnor_def, reduce_nand_def, reduce_nor_def,
   word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
   word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w,
   l2n_def,n2l_def,s2n_def,n2s_def,l2w_def,w2l_def,s2w_def,w2s_def,
   HEX_def,UNHEX_def,
   num_from_bin_list_def,num_from_oct_list_def,num_from_dec_list_def,
   num_from_hex_list_def,num_to_bin_list_def,num_to_oct_list_def,
   num_to_dec_list_def,num_to_hex_list_def,num_from_bin_string_def,
   num_from_oct_string_def,num_from_dec_string_def,num_from_hex_string_def,
   num_to_bin_string_def,num_to_oct_string_def,num_to_dec_string_def,
   num_to_hex_string_def,
   word_from_bin_list_def,word_from_oct_list_def,word_from_dec_list_def,
   word_from_hex_list_def,word_to_bin_list_def,word_to_oct_list_def,
   word_to_dec_list_def,word_to_hex_list_def,word_from_bin_string_def,
   word_from_oct_string_def,word_from_dec_string_def,word_from_hex_string_def,
   word_to_bin_string_def,word_to_oct_string_def,word_to_dec_string_def,
   word_to_hex_string_def]
  @ map l2n_pow2 [2, 8, 16, 256] @ map n2l_pow2 [2, 8, 16, 256];

val thms =
  let fun mrw th = map (REWRITE_RULE [th])
in
    (mrw TIMES_2EXP1 o mrw (GSYM bitTheory.TIMES_2EXP_def) o
     mrw (GSYM arithmeticTheory.MOD_2EXP_def)) thms
end;

fun words_compset () =
let val compset = reduceLib.num_compset()
    val _ = listSimps.list_rws compset
    val _ = add_thms thms compset
    val _ = add_conv(``fcp$dimindex:'a itself -> num``, 1, SIZES_CONV) compset
    val _ = add_conv(``words$dimword:'a itself -> num``, 1, SIZES_CONV) compset
    val _ = add_conv(``words$INT_MIN:'a itself -> num``, 1, SIZES_CONV) compset
    val _ = add_conv(``min$= : 'a word -> 'a word -> bool``, 2, word_EQ_CONV)
              compset
in
  compset
end;

val _ = add_thms thms the_compset;
val _ = add_conv(``fcp$dimindex:'a itself -> num``, 1, SIZES_CONV) the_compset;
val _ = add_conv(``words$dimword:'a itself -> num``, 1, SIZES_CONV) the_compset;
val _ = add_conv(``words$INT_MIN:'a itself -> num``, 1, SIZES_CONV) the_compset;
val _ = add_conv(``min$= : 'a word -> 'a word -> bool``, 2, word_EQ_CONV)
          the_compset;

val WORD_EVAL_CONV = CBV_CONV (words_compset());
val WORD_EVAL_RULE = CONV_RULE WORD_EVAL_CONV;
val WORD_EVAL_TAC  = CONV_TAC WORD_EVAL_CONV;

(* ------------------------------------------------------------------------- *)
(* Simpsets                                                                  *)
(* ------------------------------------------------------------------------- *)

val SYM_WORD_NEG_1 = SYM WORD_NEG_1;

local
  fun name_thy t = let val {Name,Thy,...} = dest_thy_const t in (Thy,Name) end

  fun name_thy_compare ((t1,n1),(t2,n2)) =
    case String.compare (n1,n2) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL => String.compare (t1,t2)

  fun name_thy_set l = let open Redblackset in
    addList (empty name_thy_compare, l)
  end

  val l1 =
     ["l2w","w2l","s2w","w2s","add_with_carry",
      "word_from_bin_list","word_from_oct_list","word_from_dec_list",
      "word_from_hex_list","word_to_bin_list","word_to_oct_list",
      "word_to_dec_list","word_to_hex_list","word_from_bin_string",
      "word_from_oct_string","word_from_dec_string","word_from_hex_string",
      "word_to_bin_string","word_to_oct_string","word_to_dec_string",
      "word_to_hex_string",
      "word_reduce", "reduce_and", "reduce_or", "reduce_xor",
      "reduce_nand", "reduce_nor", "reduce_xnor",
      "word_replicate", "concat_word_list", "bit_field_insert",
      "w2w","w2n","sw2sw","word_log2","word_reverse","word_msb",
      "word_join","word_concat","word_bit","word_bits","word_signed_bits",
      "word_slice","word_extract","word_asr","word_lsr","word_lsl","word_ror",
      "word_rol","word_rrx","word_lo","word_ls","word_lt","word_le"]

  val l2 =
     ["l2n","n2l","s2n","n2s","HEX","UNHEX","SBIT","BIT","BITS","BITV",
      "SLICE","TIMES_2EXP","DIVMOD_2EXP","LSB","LOG2","LOG","BITWISE",
      "BIT_REVERSE","SIGN_EXTEND", "BOOLIFY",
      "num_from_bin_list","num_from_oct_list","num_from_dec_list",
      "num_from_hex_list","num_to_bin_list","num_to_oct_list",
      "num_to_dec_list","num_to_hex_list","num_from_bin_string",
      "num_from_oct_string","num_from_dec_string","num_from_hex_string",
      "num_to_bin_string","num_to_oct_string","num_to_dec_string",
      "num_to_hex_string"]

  val s = name_thy_set
           (("min","=")::("arithmetic","DIV_2EXP")::("fcp","fcp_index")::
             map (pair "words") l1 @ map (pair "bit") l2)

  fun is_hex_digit_literal t =
        numSyntax.is_numeral t andalso
        numSyntax.int_of_term t < 16;

  fun is_ground_list t =
         let val (l,ty) = listSyntax.dest_list t in
           if ty = ``:num`` then
             Lib.all is_hex_digit_literal l
           else if ty = ``:char`` then
             Lib.all (Char.isHexDigit o stringSyntax.fromHOLchar) l
           else if ty = ``:bool`` then
             Lib.all (fn tm => term_eq F tm orelse term_eq T tm) l
           else
             wordsSyntax.is_word_type ty
         end handle HOL_ERR _ => false;

  fun is_ground_arg t =
    if pairSyntax.is_pair t then
      let val (l,r) = pairSyntax.dest_pair t in
        is_ground_arg l andalso is_ground_arg r
      end
    else
      numSyntax.is_numeral t orelse
      wordsSyntax.is_word_literal t orelse
      is_uintmax t orelse
      term_eq t T orelse
      term_eq t F orelse
      is_ground_list t orelse
      term_eq t ``bit$HEX`` orelse
      term_eq t ``bit$UNHEX`` orelse
      term_eq t ``bool$/\`` orelse
      term_eq t ``bool$\/``

  fun is_ground_fn t =
      is_comb t andalso
      let val (f,l) = strip_comb t
          val (tn as (thy,name)) = name_thy f
          val typ = type_of (prim_mk_const{Name=name,Thy=thy})
      in
         (length (fst (strip_fun typ)) = length l) andalso
         Redblackset.member(s,tn) andalso Lib.all is_ground_arg l
      end

  val alpha_rws =
   [word_lsb_n2w, word_lsb_word_T, word_msb_word_T, WORD_0_POS, WORD_L_NEG,
    word_bit_0, word_bit_0_word_T, w2w_0, sw2sw_0, sw2sw_word_T,
    word_0_n2w, word_1_n2w,
    word_len_def, word_reverse_0, word_reverse_word_T, word_log2_1, word_div_1,
    word_join_0, word_concat_0_0, word_concat_word_T, word_join_word_T,
    WORD_BITS_ZERO2, WORD_EXTRACT_ZERO2, WORD_SLICE_ZERO2,
    (REWRITE_RULE [LSB_ODD] o GSYM) LSB_def, BIT_ZERO, BITS_ZERO2]
in
  val is_known_word_size = not o is_vartype o wordsSyntax.dim_of

  fun UINT_MAX_CONV t =
    if wordsSyntax.is_n2w t then
      let val dim = wordsSyntax.dim_of t in
        if not (is_vartype dim) andalso dim <> ``:unit`` then
          PURE_REWRITE_CONV
            [GSYM (EVAL (wordsSyntax.mk_word_T dim)), SYM_WORD_NEG_1] t
        else
          raise UNCHANGED
      end
    else
      raise UNCHANGED

  fun WORD_GROUND_CONV t =
  let
    val _ = null (type_vars_in_term t) andalso is_ground_fn t orelse
              raise ERR "WORD_GROUND_CONV"
                        "Term not ground or contains type variables."
  in
    (PURE_REWRITE_CONV alpha_rws THENC
     computeLib.CBV_CONV (words_compset()) THENC UINT_MAX_CONV) t
  end

  val WORD_GROUND_ss =
    simpLib.named_merge_ss "word ground"
      [simpLib.rewrites alpha_rws,
       simpLib.conv_ss
        {conv  = K (K (CHANGED_CONV WORD_GROUND_CONV)),
         trace = 3,
         name  = "WORD_GROUND_CONV",
         key   = NONE}]
end;

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
            ISPEC `0n` pred_setTheory.IN_INSERT,
            ISPEC `^Na` pred_setTheory.IN_INSERT];

val BIT_ss =
  simpLib.named_merge_ss "bit"
    [simpLib.rewrites [BIT_ZERO],
     simpLib.std_conv_ss
       {conv = BIT_SET_CONV,
        name = "BITS_CONV",
        pats = [``bit$BIT n ^Na``]}];

(*
val WORD_ORDER_ss = simpLib.named_rewrites "word order"
  [WORD_HIGHER, WORD_HIGHER_EQ,
   WORD_GREATER, WORD_GREATER_EQ,
   WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL,
   WORD_NOT_LESS, WORD_NOT_LESS_EQUAL,
   WORD_LOWER_REFL, WORD_LOWER_EQ_REFL,
   WORD_LESS_REFL, WORD_LESS_EQ_REFL,
   word_T_not_zero, WORD_LS_word_T, WORD_LO_word_T,
   WORD_0_LS, WORD_LESS_0_word_T, WORD_L_LESS_EQ,
   WORD_LS_word_0, WORD_LO_word_0];
*)

(* ------------------------------------------------------------------------- *)

val ADD1 = arithmeticTheory.ADD1;

val WORD_LSL_NUMERAL = (GEN_ALL o SPECL [`w:'a word`,`^Na`]) WORD_MUL_LSL;

val WORD_NOT_NUMERAL =
  (SIMP_RULE std_ss [GSYM ADD1, WORD_LITERAL_ADD, word_sub_def] o
   SPEC `^n2w n`) WORD_NOT;

val WORD_NOT_NEG_NUMERAL =
  (SUC_RULE o GEN_ALL o
   SIMP_RULE arith_ss
     [GSYM ADD1, WORD_LITERAL_ADD, word_sub_def, WORD_NEG_NEG] o
   SPEC `words$word_2comp (^n2w (num$SUC n))`) WORD_NOT;

val WORD_NOT_NEG_0 = SIMP_CONV std_ss [SYM_WORD_NEG_1, WORD_NOT_0, WORD_NEG_0]
  ``words$word_1comp (words$word_2comp 0w) : 'a word``;

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

val NEG_EQ_0 = trace("metis",0) (METIS_PROVE [WORD_NEG_MUL, WORD_NEG_EQ_0])
  ``(!w:'a word. (-1w * w = 0w) = (w = 0w)) /\
    (!w:'a word. (0w = -1w * w) = (w = 0w))``;

(* ------------------------------------------------------------------------- *)

fun WORD_LITERAL_REDUCE_CONV t =
  if is_known_word_size t then
    (PURE_ONCE_REWRITE_CONV [GSYM n2w_mod]
       THENC DEPTH_CONV SIZES_CONV
       THENC numLib.REDUCE_CONV
       THENC UINT_MAX_CONV) t
  else
    numLib.REDUCE_CONV t;

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
                 [INT_MAX_def, word_L_def, word_H_def, SYM_WORD_NEG_1, w2n_n2w]
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
      CHANGED_CONV (PURE_REWRITE_CONV [WORD_H_WORD_L, SYM_WORD_NEG_1]) t

  fun WORD_UINT_MAX_CONV t =
    if is_known_word_size t then
      (CHANGED_CONV
        (PURE_REWRITE_CONV [UINT_MAX_def, word_T_def, WORD_NEG_1, w2n_n2w]
         THENC DEPTH_CONV SIZES_CONV
         THENC numLib.REDUCE_CONV)) t
    else
      raise ERR "WORD_UINT_MAX_CONV" "Not UINT_MAXw of known size"

  fun WORD_w2n_CONV t =
  let val x = wordsSyntax.dest_w2n t in
    if wordsSyntax.is_n2w x then
      if is_known_word_size x then
        conv t
      else
        CHANGED_CONV (PURE_REWRITE_CONV [word_0_n2w, word_1_n2w]) t
    else
      raise ERR "WORD_w2n_CONV" "Not w2n of word literal"
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
        raise ERR "WORD_NEG_CONV" "Negative 'a word literal"
  else
    (PURE_REWRITE_CONV [WORD_NEG_L]
       THENC PURE_ONCE_REWRITE_CONV [WORD_NEG_MUL]) t
end;

fun WORD_ARITH_EQ_CONV t =
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
        raise ERR "WORD_ARITH_EQ_CONV" "RHS is zero"
      else
        PURE_ONCE_REWRITE_CONV [GSYM WORD_EQ_SUB_ZERO] t
  else
    raise ERR "WORD_ARITH_EQ_CONV" "Not word equality"
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
     raise ERR "FIX_SIGN_OF_NEG_TERM_CONV" "Not neg term with zero RHS"
end;

fun WORD_MULT_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_mul t
   else
     raise ERR "WORD_MULT_CANON_CONV" "Can only be applied to word terms";

fun WORD_ADD_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_add t
   else
     raise ERR "WORD_ADD_CANON_CONV" "Can only be applied to word terms";

val WORD_MULT_ss =
 simpLib.merge_ss
   [simpLib.rewrites (NEG_EQ_0::word_mult_clauses),
    simpLib.std_conv_ss
      {conv = CHANGED_CONV WORD_MULT_CANON_CONV,
       name = "WORD_MULT_CANON_CONV",
       pats = [``words$word_mul (w:'a word) y``]}];

val WORD_ADD_ss =
  simpLib.std_conv_ss
    {conv = CHANGED_CONV WORD_ADD_CANON_CONV,
     name = "WORD_ADD_CANON_CONV",
     pats = [``words$word_add (w:'a word) y``]};

val WORD_SUB_ss =
 simpLib.merge_ss
   [simpLib.rewrites [word_sub_def],
    simpLib.std_conv_ss
      {conv = WORD_NEG_CONV,
       name = "WORD_NEG_CONV",
       pats = [``words$word_2comp (w:'a word)``,
               ``words$word_sub (w:'a word) y``]}];

val WORD_w2n_ss =
 simpLib.merge_ss
   [simpLib.rewrites [word_0_n2w],
    simpLib.std_conv_ss
      {conv = WORD_w2n_CONV,
       name = "WORD_w2n_CONV",
       pats = [``words$w2n (^n2w ^Na)``]}];

val WORD_UINT_MAX_ss =
 simpLib.std_conv_ss
   {conv = WORD_UINT_MAX_CONV,
    name = "WORD_UINT_MAX_CONV",
    pats = [``words$word_2comp 1w :'a word``,
            ``words$word_T :'a word``]};

val WORD_CONST_ss =
 simpLib.std_conv_ss
   {conv = WORD_CONST_CONV,
    name = "WORD_CONST_CONV",
    pats = [``words$word_L :'a word``,
            ``words$word_H :'a word``,
            ``words$word_T :'a word``]};

val WORD_ARITH_EQ_ss =
 simpLib.named_merge_ss "word arith eq"
   [simpLib.rewrites
      [WORD_LEFT_ADD_DISTRIB,WORD_RIGHT_ADD_DISTRIB,
       WORD_LSL_NUMERAL,WORD_NOT,hd (CONJUNCTS SHIFT_ZERO)],
    simpLib.std_conv_ss
      {conv = WORD_ARITH_EQ_CONV,
       name = "WORD_ARITH_EQ_CONV",
       pats = [``w = y :'a word``]}];

val WORD_ARITH_ss =
  simpLib.named_merge_ss "word arith"
    [WORD_MULT_ss, WORD_ADD_ss, WORD_SUB_ss, WORD_w2n_ss, WORD_CONST_ss];

val WORD_MULT_CONV = SIMP_CONV (pure_ss++WORD_MULT_ss) [];
val WORD_ADD_CONV  = SIMP_CONV (pure_ss++WORD_ADD_ss) [];
val WORD_SUB_CONV  = SIMP_CONV (pure_ss++WORD_SUB_ss) [];

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
                (``fcp$dimindex:'a itself->num``, 1, SIZES_CONV) cmp
  in
    cmp
  end;

val WORD_LITERAL_AND_thms =
  (SUC_RULE o REWRITE_RULE [WORD_NOT_NUMERAL]) WORD_LITERAL_AND;

val WORD_LITERAL_OR_thms =
  (SUC_RULE o REWRITE_RULE [WORD_NOT_NUMERAL]) WORD_LITERAL_OR;

val BITWISE_CONV = computeLib.CBV_CONV (bitwise_compset ());

val GSYM_WORD_OR_ASSOC = GSYM WORD_OR_ASSOC;
val GSYM_WORD_AND_ASSOC = GSYM WORD_AND_ASSOC;
val GSYM_WORD_XOR_ASSOC = GSYM WORD_XOR_ASSOC;

val WORD_OR_CLAUSES2 = REWRITE_RULE [SYM_WORD_NEG_1] WORD_OR_CLAUSES;
val WORD_AND_CLAUSES2 = REWRITE_RULE [SYM_WORD_NEG_1] WORD_AND_CLAUSES;
val WORD_XOR_CLAUSES2 = REWRITE_RULE [SYM_WORD_NEG_1] WORD_XOR_CLAUSES;

val word_or_clauses = CONJUNCTS (SPEC `a` WORD_OR_CLAUSES2);
val word_and_clauses = CONJUNCTS (SPEC `a` WORD_AND_CLAUSES2);
val word_xor_clauses = CONJUNCTS (SPEC `a` WORD_XOR_CLAUSES2);

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
in
  local
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
      assoc_mode = GenPolyCanon.R,
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
  end
  local
    val distrib = GSYM WORD_RIGHT_AND_OVER_XOR
    val WORD_REDUCE_CONV =
           PURE_REWRITE_CONV [WORD_XOR_CLAUSES2]
             THENC PURE_REWRITE_CONV [WORD_NOT_XOR, WORD_LITERAL_XOR]
             THENC BITWISE_CONV
             THENC WORD_LITERAL_REDUCE_CONV
    fun merge t = let
      val (l,r) = wordsSyntax.dest_word_xor t
    in
      if is_word_literal l andalso is_word_literal r then
        WORD_REDUCE_CONV
      else
        Conv.BINOP_CONV add_coeff THENC
        REWR_CONV distrib THENC LAND_CONV WORD_REDUCE_CONV
    end t
  in
    val gci_word_xor = GenPolyCanon.GCI
     {dest = wordsSyntax.dest_word_xor,
      is_literal = is_word_literal,
      assoc_mode = GenPolyCanon.R,
      assoc = GSYM_WORD_XOR_ASSOC,
      symassoc = WORD_XOR_ASSOC,
      comm = WORD_XOR_COMM,
      l_asscomm =
        GenPolyCanon.derive_l_asscomm GSYM_WORD_XOR_ASSOC WORD_XOR_COMM,
      r_asscomm =
        GenPolyCanon.derive_r_asscomm GSYM_WORD_XOR_ASSOC WORD_XOR_COMM,
      non_coeff = non_coeff,
      merge = merge,
      postnorm = PURE_REWRITE_CONV [WORD_XOR_CLAUSES2],
      left_id = hd word_xor_clauses,
      right_id = hd (tl word_xor_clauses),
      reducer = WORD_REDUCE_CONV}
  end
end;

fun WORD_COMP_CONV t =
let val x = wordsSyntax.dest_word_1comp t in
  if is_known_word_size t then
    if is_word_zero x then
      PURE_REWRITE_CONV [REWRITE_RULE [SYM_WORD_NEG_1] WORD_NOT_0] t
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
     raise ERR "WORD_AND_CANON_CONV" "Can only be applied to word terms";

fun WORD_OR_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_or t
   else
     raise ERR "WORD_OR_CANON_CONV" "Can only be applied to word terms";

fun WORD_XOR_CANON_CONV t =
   if wordsSyntax.is_word_type (type_of t) then
     GenPolyCanon.gencanon gci_word_xor t
   else
     raise ERR "WORD_XOR_CANON_CONV" "Can only be applied to word terms";

val WORD_COMP_ss =
  simpLib.merge_ss
   [simpLib.rewrites
      [WORD_DE_MORGAN_THM, WORD_NOT_NOT, WORD_NOT_NEG_0, SYM_WORD_NEG_1,
       REWRITE_RULE [GSYM arithmeticTheory.PRE_SUB1] WORD_NOT_NEG_NUMERAL],
    simpLib.std_conv_ss
      {conv = reduceLib.PRE_CONV,
       name = "PRE_CONV",
       pats  = [``prim_rec$PRE ^Na``]},
    simpLib.std_conv_ss
      {conv = WORD_COMP_CONV,
       name = "WORD_COMP_CONV",
       pats = [``words$word_1comp (^n2w n) :'a word``]}];

val WORD_AND_ss =
  simpLib.merge_ss
   [simpLib.rewrites [WORD_AND_CLAUSES2, WORD_AND_COMP, WORD_NAND_NOT_AND,
       WORD_AND_ABSORD, ONCE_REWRITE_RULE [WORD_AND_COMM] WORD_AND_ABSORD],
    simpLib.std_conv_ss
      {conv = WORD_AND_CANON_CONV,
       name = "WORD_AND_CANON_CONV",
       pats = [``words$word_and (w:'a word) y``]}];

val WORD_XOR_ss =
  simpLib.merge_ss
   [simpLib.rewrites [WORD_XOR_CLAUSES2, WORD_NOT_XOR, WORD_XNOR_NOT_XOR],
    simpLib.std_conv_ss
      {conv = WORD_XOR_CANON_CONV,
       name = "WORD_XOR_CANON_CONV",
       pats = [``words$word_xor (w:'a word) y``]}];

val WORD_OR_ss =
  let
    val thm = REWRITE_RULE [SYM_WORD_NEG_1] WORD_OR_COMP
  in
    simpLib.merge_ss
      [simpLib.rewrites
         [WORD_OR_CLAUSES2, WORD_NOR_NOT_OR,
          thm, ONCE_REWRITE_RULE [WORD_OR_COMM] thm],
       simpLib.std_conv_ss
         {conv = WORD_OR_CANON_CONV,
          name = "WORD_OR_CANON_CONV",
          pats = [``words$word_or (w:'a word) y``]}]
  end;

val WORD_LOGIC_ss = simpLib.named_merge_ss "word logic"
  [WORD_COMP_ss,WORD_AND_ss,WORD_OR_ss,WORD_XOR_ss];

val WORD_LOGIC_CONV = SIMP_CONV (bool_ss++WORD_LOGIC_ss)
  [WORD_LEFT_AND_OVER_OR,WORD_RIGHT_AND_OVER_OR,REFL_CLAUSE];

(* ------------------------------------------------------------------------- *)

val ROL_ROR_MOD_RWT = prove(
  ``!n w:'a word. fcp$dimindex (:'a) <= n ==>
      (words$word_rol w n =
       words$word_rol w (arithmetic$MOD n (fcp$dimindex (:'a)))) /\
      (words$word_ror w n =
       words$word_ror w (arithmetic$MOD n (fcp$dimindex (:'a))))``,
  SRW_TAC [] [Once (GSYM ROL_MOD), Once (GSYM ROR_MOD)]);

val WORD_SHIFT_ss =
  simpLib.named_rewrites "word shift"
    ([SHIFT_ZERO, ZERO_SHIFT, word_rrx_0, word_rrx_word_T, lsr_1_word_T,
      LSL_ADD, LSR_ADD, ASR_ADD, ROR_ROL, ROR_ADD, ROL_ADD, ROL_ROR_MOD_RWT,
      WORD_ADD_LSL, GSYM WORD_2COMP_LSL,
      GSYM LSL_BITWISE, GSYM LSR_BITWISE, GSYM ROR_BITWISE, GSYM ROL_BITWISE,
      LSL_LIMIT, LSR_LIMIT, ASR_LIMIT] @
    map (REWRITE_RULE [SYM_WORD_NEG_1])
     [ASR_UINT_MAX, ROR_UINT_MAX,
      (REWRITE_RULE [ROR_UINT_MAX] o
         SPEC `words$word_T`) word_rol_def]);

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
     wordsSyntax.mk_word_lsl (t, numSyntax.mk_numeral n);

fun sum_n l = foldl (fn (a,b) => wordsSyntax.mk_word_add (b,a)) (hd l) (tl l);

fun WORD_MUL_LSL_CONV tm = let
  val (l,r) = wordsSyntax.dest_word_mul tm
  val v = wordsSyntax.dest_word_literal l
in
  if v = Arbnum.zero then
    REWR_CONV (hd word_mult_clauses) tm
  else let
    val _ = not (wordsSyntax.is_word_literal r) orelse
              raise ERR "WORD_MUL_LSL_CONV" "Not a term of the form: n2w n * x"
    val t' = sum_n (List.map (shift_n r) (word2list l))
  in
    EQT_ELIM (SIMP_CONV (std_ss++WORD_ARITH_ss) [WORD_MUL_LSL] (mk_eq (tm,t')))
  end
end;

val WORD_MUL_LSL_ss =
  simpLib.named_merge_ss "word mul lsl"
    [simpLib.std_conv_ss
      {conv = WORD_MUL_LSL_CONV,
       name = "WORD_MUL_LSL_CONV",
       pats = [``words$word_mul (^n2w ^Na) w:'a word``]}];

(* ------------------------------------------------------------------------- *)

val LET_RULE = SIMP_RULE (bool_ss++boolSimps.LET_ss) [];
val OR_AND_COMM_RULE = ONCE_REWRITE_RULE [WORD_ADD_COMM, WORD_OR_COMM];

val WORD_EXTRACT_ss =
  simpLib.named_merge_ss "word extract"
   [simpLib.std_conv_ss
      {conv = WORD_EVAL_CONV,
       name = "WORD_EVAL_CONV",
       pats = [``words$word_replicate ^Na (w:'a word):'b word``]},
   simpLib.rewrites
    ([WORD_EXTRACT_ZERO, WORD_EXTRACT_ZERO2, WORD_EXTRACT_ZERO3,
      WORD_EXTRACT_LSL, WORD_EXTRACT_LSL2, word_extract_eq_n2w, word_concat_def,
      LET_RULE word_join_def, word_rol_def, LET_RULE word_ror, word_asr,
      word_lsr_n2w, WORD_EXTRACT_COMP_THM, WORD_EXTRACT_MIN_HIGH,
      EXTRACT_JOIN, EXTRACT_JOIN_LSL, EXTRACT_JOIN_ADD, EXTRACT_JOIN_ADD_LSL,
      OR_AND_COMM_RULE EXTRACT_JOIN, OR_AND_COMM_RULE EXTRACT_JOIN_LSL,
      OR_AND_COMM_RULE EXTRACT_JOIN_ADD, OR_AND_COMM_RULE
      EXTRACT_JOIN_ADD_LSL, GSYM WORD_EXTRACT_OVER_BITWISE,
      (GEN_ALL o ISPEC `words$word_extract h l :'a word -> 'b word`) COND_RAND,
      WORD_BITS_EXTRACT, WORD_w2w_EXTRACT, sw2sw_w2w, word_lsb, word_msb] @
      map (REWRITE_RULE [WORD_BITS_EXTRACT])
        [WORD_ALL_BITS, WORD_SLICE_THM, WORD_BIT_BITS])];

(* ------------------------------------------------------------------------- *)

local
  val ssfrags = [WORD_LOGIC_ss, WORD_ARITH_ss, WORD_SHIFT_ss, WORD_GROUND_ss,
                 BIT_ss, SIZES_ss]
in
  val WORD_ss = simpLib.named_merge_ss "words" ssfrags
  val _ = augment_srw_ss ssfrags
end

val WORD_CONV = SIMP_CONV (std_ss++WORD_ss++WORD_EXTRACT_ss)
  [WORD_LEFT_ADD_DISTRIB, WORD_RIGHT_ADD_DISTRIB,
   WORD_LEFT_AND_OVER_OR, WORD_RIGHT_AND_OVER_OR];

(* ------------------------------------------------------------------------- *)

val LESS_THM = SUC_RULE prim_recTheory.LESS_THM;

val LESS_COR =
  [``(prim_rec$< m (arithmetic$NUMERAL (arithmetic$BIT1 n))) ==> (P:bool)``,
   ``(prim_rec$< m (arithmetic$NUMERAL (arithmetic$BIT2 n))) ==> (P:bool)``]
     |> map (GEN_ALL o REWRITE_CONV [LESS_THM, DISJ_IMP_THM]) |> LIST_CONJ;

fun dest_strip t =
let val (l,r) = strip_comb t in
  (fst (dest_const l), r)
end;

local
  val word_n2w_le = Q.prove(
    `!a. w2n (n2w a :'a word) <= a MOD dimword(:'a)`,
    SIMP_TAC std_ss [w2n_n2w])

  val word_n2w_le2 = Q.prove(
    `!a. w2n (n2w a :'a word) <= a`,
    SIMP_TAC std_ss [w2n_n2w, bitTheory.MOD_LEQ, ZERO_LT_dimword])

  val word_extract_le = Q.prove(
    `!a:'a word h l. w2n ((h >< l) a) <= w2n a`,
    Cases THEN SRW_TAC [] [word_extract_n2w]
    THEN SRW_TAC [] [bitTheory.BITS_COMP_THM2, MOD_DIMINDEX]
    THEN SRW_TAC [] [arithmeticTheory.MIN_DEF, bitTheory.BITS_LEQ])

  val word_add_le = Q.prove(
    `!a:'a word b. w2n (a + b) <= w2n a + w2n b`,
    Cases THEN Cases
    THEN SIMP_TAC std_ss [bitTheory.MOD_LEQ, word_add_def, w2n_n2w,
           ZERO_LT_dimword])

  val word_mul_le = Q.prove(
    `!a:'a word b. w2n (a * b) <= w2n a * w2n b`,
    Cases THEN Cases
    THEN SIMP_TAC std_ss [bitTheory.MOD_LEQ, word_mul_def, w2n_n2w,
           ZERO_LT_dimword])

  val word_lsl_le = Q.prove(
    `!a:'a word b. w2n (a << b) <= w2n a * 2 ** b`,
    Cases THEN SRW_TAC [] [word_lsl_n2w, bitTheory.MOD_LEQ, ZERO_LT_dimword])

  val word_div_le = Q.prove(
    `!a:'a word b.
       0 < b MOD dimword (:'a) ==>
       w2n (a // n2w b) <= w2n a DIV b MOD dimword (:'a)`,
    Cases THEN STRIP_TAC
    THEN Cases_on `b MOD dimword (:'a) = 1`
    THENL
      [SRW_TAC [numSimps.ARITH_ss] [word_div_def, w2n_n2w],
       Cases_on `n = 0`
       THEN SRW_TAC [numSimps.ARITH_ss] [word_div_def, w2n_n2w,
            arithmeticTheory.ZERO_DIV, bitTheory.MOD_LEQ, ZERO_LT_dimword]])

  val word_div_le2_lem = Q.prove(
    `!n. 0 < (SUC (2 * n)) MOD dimword (:'a)`,
    SRW_TAC [] [arithmeticTheory.ADD1, bitTheory.MOD_PLUS_1, ZERO_LT_dimword,
                DECIDE ``0n < n = (n <> 0)``]
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN ASM_SIMP_TAC arith_ss
         [arithmeticTheory.EXP, GSYM arithmeticTheory.MOD_COMMON_FACTOR,
          bitTheory.ZERO_LT_TWOEXP, dimword_def, GSYM arithmeticTheory.ADD1]
    THEN `ODD (SUC (2 * n MOD 2 ** m))`
      by (REWRITE_TAC [arithmeticTheory.ODD_EXISTS]
         THEN Q.EXISTS_TAC `n MOD 2 ** m` THEN REWRITE_TAC [])
    THEN RULE_ASSUM_TAC (SIMP_RULE std_ss
           [arithmeticTheory.ODD_EVEN, arithmeticTheory.EVEN_EXISTS])
    THEN POP_ASSUM (Q.SPEC_THEN `2 ** m` ASSUME_TAC)
    THEN ASM_REWRITE_TAC [])

  val word_div_le2 = Q.prove(
    `!a:'a word b. ODD b ==> w2n (a // n2w b) <= w2n a`,
    Cases THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC (CONJUNCT2 (SPEC_ALL arithmeticTheory.EVEN_ODD_EXISTS))
    THEN POP_ASSUM SUBST1_TAC
    THEN SRW_TAC [numSimps.ARITH_ss] [word_div_def, w2n_n2w]
    THEN `n DIV SUC (2 * m) MOD dimword (:'a) <= n`
      by SIMP_TAC std_ss [arithmeticTheory.DIV_LESS_EQ, word_div_le2_lem]
    THEN SRW_TAC [numSimps.ARITH_ss] [])

  val word_extract_order1 = Q.prove(
    `!a b h l. w2n a < b ==> w2n ((h >< l) a) < b`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n ((h >< l) a)`, `w2n a`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
    THEN ASM_REWRITE_TAC [word_extract_le])

  val word_extract_order2 = Q.prove(
    `!a b h l. w2n a <= b ==> w2n ((h >< l) a) <= b`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n ((h >< l) a)`, `w2n a`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_REWRITE_TAC [word_extract_le])

  val word_add_order1 = Q.prove(
    `!a b m n. w2n a <= m /\ w2n b <= n ==> w2n (a + b) <= m + n`,
    REPEAT STRIP_TAC
    THEN `w2n a + w2n b <= m + n` by DECIDE_TAC
    THEN Q.SPECL_THEN [`w2n (a + b)`, `w2n a + w2n b`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_REWRITE_TAC [word_add_le])

  val word_add_order2 = Q.prove(
    `!a b m n. w2n a <= m /\ w2n b < n ==> w2n (a + b) < m + n`,
    REPEAT STRIP_TAC
    THEN `w2n a + w2n b < m + n` by DECIDE_TAC
    THEN Q.SPECL_THEN [`w2n (a + b)`, `w2n a + w2n b`]
         MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
    THEN ASM_REWRITE_TAC [word_add_le])

  val word_add_order3 = Q.prove(
    `!a b m n. w2n a < m /\ w2n b <= n ==> w2n (a + b) < m + n`,
    REPEAT STRIP_TAC
    THEN `w2n a + w2n b < m + n` by DECIDE_TAC
    THEN Q.SPECL_THEN [`w2n (a + b)`, `w2n a + w2n b`]
         MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
    THEN ASM_REWRITE_TAC [word_add_le])

  val word_add_order4 = Q.prove(
    `!a b m n. w2n a < m /\ w2n b < n ==> w2n (a + b) < m + n - 1`,
    REPEAT STRIP_TAC
    THEN `w2n a + w2n b < m + n - 1` by DECIDE_TAC
    THEN Q.SPECL_THEN [`w2n (a + b)`, `w2n a + w2n b`]
         MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
    THEN ASM_REWRITE_TAC [word_add_le])

  val word_mul_order1 = Q.prove(
    `!a b m n. w2n a <= m /\ w2n b <= n ==> w2n (a * b) <= m * n`,
    REPEAT STRIP_TAC
    THEN `w2n a * w2n b <= m * n`
      by ASM_SIMP_TAC std_ss [arithmeticTheory.LESS_MONO_MULT2]
    THEN Q.SPECL_THEN [`w2n (a * b)`, `w2n a * w2n b`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_REWRITE_TAC [word_mul_le])

  val word_mul_order2 = Q.prove(
    `!a b m n. w2n a <= m /\ w2n b < n ==> w2n (a * b) <= m * n`,
    REPEAT STRIP_TAC
    THEN `w2n a * w2n b <= m * n`
      by ASM_SIMP_TAC arith_ss [arithmeticTheory.LESS_MONO_MULT2]
    THEN Q.SPECL_THEN [`w2n (a * b)`, `w2n a * w2n b`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_SIMP_TAC arith_ss [word_mul_le])

  val word_mul_order3 = Q.prove(
    `!a b m n. w2n a < m /\ w2n b <= n ==> w2n (a * b) <= m * n`,
    REPEAT STRIP_TAC
    THEN `w2n a * w2n b <= m * n`
      by ASM_SIMP_TAC arith_ss [arithmeticTheory.LESS_MONO_MULT2]
    THEN Q.SPECL_THEN [`w2n (a * b)`, `w2n a * w2n b`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_SIMP_TAC arith_ss [word_mul_le])

  val word_mul_order4 = Q.prove(
    `!a b m n. w2n a < m /\ w2n b < n ==> w2n (a * b) <= m * n`,
    REPEAT STRIP_TAC
    THEN `w2n a * w2n b <= m * n`
      by ASM_SIMP_TAC arith_ss [arithmeticTheory.LESS_MONO_MULT2]
    THEN Q.SPECL_THEN [`w2n (a * b)`, `w2n a * w2n b`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_SIMP_TAC arith_ss [word_mul_le])

  val word_lsl_order1 = Q.prove(
    `!a:'a word b n. w2n a < n ==> w2n (a << b) < n * 2 ** b`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n (a << b)`, `w2n a * 2 ** b`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
    THEN ASM_REWRITE_TAC [arithmeticTheory.LT_MULT_RCANCEL,
           bitTheory.ZERO_LT_TWOEXP, word_lsl_le])

  val word_lsl_order2 = Q.prove(
    `!a:'a word b n. w2n a <= n ==> w2n (a << b) <= n * 2 ** b`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n (a << b)`, `w2n a * 2 ** b`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_REWRITE_TAC [arithmeticTheory.LE_MULT_RCANCEL,
           bitTheory.ZERO_LT_TWOEXP, word_lsl_le])

  val word_div_order_lem =
    word_div_le |> SPEC_ALL
                |> Q.DISCH `b < dimword (:'a)`
                |> SIMP_RULE arith_ss [];

  val word_div_order1 = Q.prove(
    `!a:'a word b n.
       0 < b /\ b < dimword (:'a) /\ w2n a <= n ==>
       w2n (a // n2w b) <= n DIV b`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n (a // n2w b)`, `w2n a DIV b MOD dimword (:'a)`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_SIMP_TAC arith_ss [arithmeticTheory.DIV_LE_MONOTONE,
           word_div_order_lem])

  val word_div_order2 = Q.prove(
    `!a:'a word b n.
       0 < b /\ b < dimword (:'a) /\ w2n a < n ==>
       w2n (a // n2w b) <= n DIV b`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n (a // n2w b)`, `w2n a DIV b MOD dimword (:'a)`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_SIMP_TAC arith_ss [arithmeticTheory.DIV_LE_MONOTONE,
           word_div_order_lem])

  val word_div_order3 = Q.prove(
    `!a:'a word b n.
       ODD b /\ w2n a <= n ==> w2n (a // n2w b) <= n`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n (a // n2w b)`, `w2n a`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
    THEN ASM_SIMP_TAC std_ss [word_div_le2])

  val word_div_order4 = Q.prove(
    `!a:'a word b n.
       ODD b /\ w2n a < n ==> w2n (a // n2w b) < n`,
    REPEAT STRIP_TAC
    THEN Q.SPECL_THEN [`w2n (a // n2w b)`, `w2n a`]
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
    THEN ASM_SIMP_TAC std_ss [word_div_le2])

  val word_type = wordsSyntax.dest_word_type o type_of
  val arb_thm = boolSyntax.arb |> Term.inst [alpha |-> bool] |> ASSUME
  val SIZE_RULE = CONV_RULE (DEPTH_CONV SIZES_CONV)
  val RAND_REDUCE_RULE = CONV_RULE (RAND_CONV numLib.REDUCE_CONV)

  datatype bound = LE_BOUND of Arbnum.num
                 | LT_BOUND of Arbnum.num
                 | NO_BOUND

  fun bnd thm = let val tm = concl thm in
                  case Lib.total numSyntax.dest_less tm
                  of SOME (_,n) =>
                       (case Lib.total numSyntax.dest_numeral n
                        of SOME v => LT_BOUND v
                         | NONE => NO_BOUND)
                   | NONE =>
                       (case Lib.total numSyntax.dest_leq tm
                          of SOME (_,n) =>
                               (case Lib.total numSyntax.dest_numeral n
                                of SOME v => LE_BOUND v
                                 | NONE => NO_BOUND)
                           | NONE => NO_BOUND)
                end

  (* bounds for: + * n2w >< // << *)
  fun mk_bounds_thm t = let
          val w = wordsSyntax.dest_w2n t
          val thm1 = SIZE_RULE (Drule.ISPEC w w2n_lt)
          fun default () = case bnd thm1
                           of LT_BOUND _ => thm1
                            | _ => raise ERR "mk_bounds_thm"
                                             "can't compute bound"
          fun sub_bound x = mk_bounds_thm (wordsSyntax.mk_w2n x)
                              handle HOL_ERR _ => arb_thm
        in
          case Lib.total dest_strip w
          of SOME ("word_extract", args as [h,l,a]) => let
                  val thm2 = WORD_EXTRACT_LT
                               |> Thm.INST_TYPE
                                   [alpha |-> word_type a, beta |-> word_type w]
                               |> Drule.SPECL args
                               |> RAND_REDUCE_RULE
                  val thm3 = sub_bound a
                  fun thm3_order th b =
                        MATCH_MP
                          (th |> Thm.INST_TYPE
                                   [alpha |-> word_type a, beta |-> word_type w]
                              |> Drule.SPECL [a, numSyntax.mk_numeral b, h, l])
                          thm3
                  val thm3_order1 = thm3_order word_extract_order1
                  val thm3_order2 = thm3_order word_extract_order2
                in
                  case (bnd thm1, bnd thm2, bnd thm3)
                  of (LT_BOUND _, NO_BOUND,   NO_BOUND)   => thm1
                   | (NO_BOUND,   LT_BOUND _, NO_BOUND)   => thm2
                   | (NO_BOUND,   NO_BOUND,   LT_BOUND b1) => thm3_order1 b1
                   | (NO_BOUND,   NO_BOUND,   LE_BOUND b1) => thm3_order2 b1
                   | (LT_BOUND b1, LT_BOUND b2, NO_BOUND) =>
                        if Arbnum.<=(b1, b2) then thm1 else thm2
                   | (LT_BOUND b1, NO_BOUND, LT_BOUND b2) =>
                        if Arbnum.<=(b1, b2) then thm1 else thm3_order1 b2
                   | (NO_BOUND, LT_BOUND b1, LT_BOUND b2) =>
                        if Arbnum.<=(b1, b2) then thm2 else thm3_order1 b2
                   | (LT_BOUND b1, NO_BOUND, LE_BOUND b2) =>
                        if Arbnum.<=(b1, Arbnum.plus1 b2) then
                          thm1
                        else
                          thm3_order2 b2
                   | (NO_BOUND, LT_BOUND b1, LE_BOUND b2) =>
                        if Arbnum.<=(b1, Arbnum.plus1 b2) then
                          thm2
                        else
                          thm3_order2 b2
                   | (LT_BOUND b1, LT_BOUND b2, LT_BOUND b3) =>
                        if Arbnum.<=(b1, b2) then
                          if Arbnum.<=(b1, b3) then thm1 else thm3_order1 b3
                        else
                          if Arbnum.<=(b2, b3) then thm2 else thm3_order1 b3
                   | (LT_BOUND b1, LT_BOUND b2, LE_BOUND b3) =>
                        if Arbnum.<=(b1, b2) then
                          if Arbnum.<=(b1, Arbnum.plus1 b3) then
                            thm1
                          else
                            thm3_order1 b3
                        else
                          if Arbnum.<=(b2, Arbnum.plus1 b3) then
                            thm2
                          else
                            thm3_order1 b3
                   | _ => raise ERR "mk_bounds_thm" "can't compute bound"
                end
           | SOME ("n2w", [n]) => let
                  val thm2 = if is_known_word_size w then
                               word_n2w_le
                                 |> Thm.SPEC n
                                 |> Thm.INST_TYPE
                                      [alpha |-> wordsSyntax.dim_of w]
                                 |> SIZE_RULE
                                 |> numLib.REDUCE_RULE
                             else
                               word_n2w_le2 |> Thm.SPEC n
                in
                  case (bnd thm1, bnd thm2)
                  of (LT_BOUND _, NO_BOUND) => thm1
                   | (NO_BOUND, LE_BOUND _) => thm2
                   | (LT_BOUND b1, LE_BOUND b2) =>
                        if Arbnum.<=(b1, Arbnum.plus1 b2) then thm1 else thm2
                   | _ => raise ERR "mk_bounds_thm" "can't compute bound"
                end
           | SOME ("word_add", [a,b]) => let
                  val thm2 = sub_bound a
                  fun f th thm3 = MATCH_MP th (CONJ thm2 thm3)
                                    |> RAND_REDUCE_RULE
                in
                  case (bnd thm1, bnd thm2)
                  of (LT_BOUND _, NO_BOUND) => thm1
                   | (NO_BOUND, LT_BOUND _) =>
                        let val thm3 = sub_bound b in
                          case bnd thm3
                          of LT_BOUND _ => f word_add_order4 thm3
                           | LE_BOUND _ => f word_add_order3 thm3
                           | NO_BOUND =>
                               raise ERR "mk_bounds_thm" "can't compute bound"
                        end
                   | (NO_BOUND, LE_BOUND _) =>
                        let val thm3 = sub_bound b in
                          case bnd thm3
                          of LT_BOUND _ => f word_add_order2 thm3
                           | LE_BOUND _ => f word_add_order1 thm3
                           | NO_BOUND =>
                               raise ERR "mk_bounds_thm" "can't compute bound"
                        end
                   | (LT_BOUND b1, LT_BOUND b2) =>
                        if Arbnum.<=(b1, b2) then
                          thm1
                        else let val thm3 = sub_bound b in
                          case bnd thm3
                          of LT_BOUND b3 =>
                               if Arbnum.<(b1, Arbnum.+(b2,b3)) then
                                 thm1
                               else
                                 f word_add_order4 thm3
                           | LE_BOUND b3 =>
                               if Arbnum.<=(b1, Arbnum.+(b2,b3)) then
                                 thm1
                               else
                                 f word_add_order3 thm3
                           | NO_BOUND =>
                               raise ERR "mk_bounds_thm" "can't compute bound"
                        end
                   | (LT_BOUND b1, LE_BOUND b2) =>
                        if Arbnum.<=(b1, Arbnum.plus1 b2) then
                          thm1
                        else let val thm3 = sub_bound b in
                          case bnd thm3
                          of LT_BOUND b3 =>
                               if Arbnum.<=(b1, Arbnum.+(b2,b3)) then
                                 thm1
                               else
                                 f word_add_order2 thm3
                           | LE_BOUND b3 =>
                               if Arbnum.<=(b1, Arbnum.+(b2,b3)) then
                                 thm1
                               else
                                 f word_add_order1 thm3
                           | NO_BOUND =>
                               raise ERR "mk_bounds_thm" "can't compute bound"
                        end
                   | _ => raise ERR "mk_bounds_thm" "can't compute bound"
                end
           | SOME ("word_mul", [a,b]) => let
                  val thm2 = sub_bound a
                in
                  case bnd thm2
                  of LT_BOUND b2 => let
                         val thm3 = sub_bound b
                         fun f th = MATCH_MP th (CONJ thm2 thm3)
                                      |> RAND_REDUCE_RULE
                       in
                         case (bnd thm1, bnd thm3)
                         of (NO_BOUND, LT_BOUND b3) => f word_mul_order4
                          | (NO_BOUND, LE_BOUND b3) => f word_mul_order3
                          | (LT_BOUND b1, LT_BOUND b3) =>
                              if Arbnum.<=(b1,Arbnum.plus1 (Arbnum.*(b2,b3)))
                              then thm1 else f word_mul_order4
                          | (LT_BOUND b1, LE_BOUND b3) =>
                              if Arbnum.<=(b1,Arbnum.plus1 (Arbnum.*(b2,b3)))
                              then thm1 else f word_mul_order3
                          | (LT_BOUND _, NO_BOUND) => thm1
                          | _ => raise ERR "mk_bounds_thm" "can't compute bound"
                       end
                   | LE_BOUND b2 => let
                         val thm3 = sub_bound b
                         fun f th = MATCH_MP th (CONJ thm2 thm3)
                                      |> RAND_REDUCE_RULE
                       in
                         case (bnd thm1, bnd thm3)
                         of (NO_BOUND, LT_BOUND b3) => f word_mul_order2
                          | (NO_BOUND, LE_BOUND b3) => f word_mul_order1
                          | (LT_BOUND b1, LT_BOUND b3) =>
                              if Arbnum.<=(b1,Arbnum.plus1 (Arbnum.*(b2,b3)))
                              then thm1 else f word_mul_order2
                          | (LT_BOUND b1, LE_BOUND b3) =>
                              if Arbnum.<=(b1,Arbnum.plus1 (Arbnum.*(b2,b3)))
                              then thm1 else f word_mul_order1
                          | (LT_BOUND _, NO_BOUND) => thm1
                          | _ => raise ERR "mk_bounds_thm" "can't compute bound"
                       end
                   | NO_BOUND => default ()
                end
           | SOME ("word_lsl", args as [a,b]) =>
               (case Lib.total numLib.dest_numeral b
                of SOME v => let
                        val thm2 = sub_bound a
                        fun f b = Arbnum.*(b,Arbnum.pow(Arbnum.two,v))
                        fun g thm = MATCH_MP (Drule.ISPECL args thm) thm2
                                      |> RAND_REDUCE_RULE
                      in
                        case (bnd thm1, bnd thm2)
                        of (NO_BOUND, LT_BOUND _) => g word_lsl_order1
                         | (NO_BOUND, LE_BOUND _) => g word_lsl_order2
                         | (LT_BOUND b1, LT_BOUND b2) =>
                             if Arbnum.<=(b1,f b2) then
                               thm1
                             else
                               g word_lsl_order1
                         | (LT_BOUND b1, LE_BOUND b2) =>
                             if Arbnum.<=(b1,Arbnum.plus1 (f b2)) then
                               thm1
                             else
                               g word_lsl_order2
                         | _ => raise ERR "mk_bounds_thm" "can't compute bound"
                      end
                 | NONE => default ())
           | SOME ("word_div", [a,b]) =>
               (case Lib.total wordsSyntax.dest_n2w b
                of SOME (n, ty) =>
                   (case (Lib.total numLib.dest_numeral n,
                          Lib.total fcpLib.index_to_num ty)
                    of (SOME v, SOME w) =>
                         if v = Arbnum.zero orelse
                            Arbnum.>=(v, Arbnum.pow (Arbnum.two, w))
                         then
                           default ()
                         else let
                           val thm2 = sub_bound a
                           fun thm3 () =
                                 numSyntax.mk_less (numSyntax.zero_tm, n)
                                   |> bossLib.DECIDE
                           fun thm4 () = numSyntax.mk_less (n,
                                                 wordsSyntax.mk_dimword ty)
                                           |> WORD_EVAL_CONV
                                           |> EQT_ELIM
                           fun g thm = MATCH_MP (Drule.ISPECL [a,n] thm)
                                         (LIST_CONJ [thm3 (), thm4 (), thm2])
                                         |> RAND_REDUCE_RULE
                         in
                           case bnd thm2
                           of LT_BOUND _ => g word_div_order2
                            | LE_BOUND _ => g word_div_order1
                            | _ => raise ERR "mk_bounds_thm"
                                             "can't compute bound"
                         end
                     | (SOME v, NONE) =>
                         if Arbnum.mod2 v = Arbnum.zero then
                           raise ERR "mk_bounds_thm" "can't compute bound"
                         else let
                           val thm2 = sub_bound a
                           fun thm3 () = numSyntax.mk_odd n
                                           |> numLib.REDUCE_CONV
                                           |> EQT_ELIM
                           fun g thm = MATCH_MP (Drule.ISPECL [a,n] thm)
                                          (CONJ (thm3 ()) thm2)
                         in
                           case bnd thm2
                           of LT_BOUND _ => g word_div_order4
                            | LE_BOUND _ => g word_div_order3
                            | _ => raise ERR "mk_bounds_thm"
                                             "can't compute bound"
                         end
                     | _ => default ())
                 | NONE => default ())
           | _ => default ()
        end
in
  fun mk_bounds_thms t =
  let val l = t |> find_terms wordsSyntax.is_w2n
                |> Lib.mk_set
                |> Lib.mapfilter mk_bounds_thm
  in
    if null l then
      TRUTH
    else
      LIST_CONJ l
  end
end;

val EXISTS_NUMBER = prove(
  ``!P. (?w:'a word. P (words$w2n w)) = (?n. n < words$dimword(:'a) /\ P n)``,
  STRIP_TAC THEN EQ_TAC THEN SRW_TAC [] []
    THENL [Q.EXISTS_TAC `words$w2n w`, Q.EXISTS_TAC `words$n2w n`]
    THEN ASM_SIMP_TAC std_ss [w2n_lt, w2n_n2w]);

fun EXISTS_WORD_CONV t =
  if is_exists t then
    let val v = fst (dest_exists t) in
      if wordsSyntax.is_word_type (type_of v) then
        (UNBETA_CONV v THENC SIMP_CONV (std_ss++SIZES_ss) [EXISTS_NUMBER]) t
      else
        raise ERR "EXISTS_WORD_CONV" "Not an \"exists word\" term."
    end
  else
    raise ERR "EXISTS_WORD_CONV" "Not an exists term.";

local
  val word_join = SIMP_RULE (std_ss++boolSimps.LET_ss) [] word_join_def
  val rw = [word_0,word_T,word_L,word_xor_def,word_or_def,word_and_def,
            word_1comp_def, REWRITE_RULE [SYM_WORD_NEG_1] word_T,
            pred_setTheory.NOT_IN_EMPTY,
            ISPEC `0n` pred_setTheory.IN_INSERT,
            ISPEC `^Na` pred_setTheory.IN_INSERT,
            fcpTheory.FCP_UPDATE_def,LESS_COR,sw2sw,w2w,word_replicate_def,
            word_join,word_concat_def,word_reverse_def,word_modify_def,
            word_lsl_def,word_lsr_def,word_asr_def,word_ror_def,
            word_rol_def,word_rrx_def,word_msb_def,word_lsb_def,
            word_extract_def,word_bits_def,word_slice_def,word_bit_def,
            word_signed_bits_def,
            ``(if b then x:'a word else y) ' i = if b then x ' i else y ' i``
              |> simpLib.SIMP_PROVE std_ss [COND_RAND,COND_RATOR] |> GEN_ALL]
  val thms = [WORD_ADD_LEFT_LO, WORD_ADD_LEFT_LS,
              WORD_ADD_RIGHT_LS, WORD_ADD_RIGHT_LO]
  val thms2 = map (GEN_ALL o SPEC `^n2w n`)
               [WORD_ADD_LEFT_LO2, WORD_ADD_LEFT_LS2,
                WORD_ADD_RIGHT_LO2, WORD_ADD_RIGHT_LS2]
  val rw3 = [WORD_LT_LO, WORD_LE_LS, WORD_GREATER, WORD_GREATER_EQ,
             CONV_RULE WORD_ARITH_CONV WORD_LS_T,
             CONV_RULE WORD_ARITH_CONV WORD_LESS_EQ_H] @
             map (SPECL [`^n2w m`, `^n2w n`]) thms @
             thms2 @ map (ONCE_REWRITE_RULE [WORD_ADD_COMM]) thms2
  val rw4 = [SPECL [`w:'a word`,`^n2w m`, `^n2w n`] WORD_ADD_EQ_SUB,
             SPECL [`w:'a word`,`words$word_2comp (^n2w m)`, `^n2w n`]
               WORD_ADD_EQ_SUB,
             REWRITE_RULE [GSYM w2n_11, word_0_n2w] NOT_INT_MIN_ZERO,
             REWRITE_RULE [WORD_LO, word_0_n2w] ZERO_LO_INT_MIN,
             WORD_LO, WORD_LS, WORD_HI, WORD_HS, GSYM w2n_11]
  val DECIDE_CONV = EQT_INTRO o DECIDE
  fun EQ_CONV t = (if term_eq T t orelse term_eq F t then
                     ALL_CONV else NO_CONV) t
  val trace_word_decide = ref 0
  val _ = Feedback.register_trace ("word decide", trace_word_decide, 1)
in
  val WORD_BIT_EQ_ss =
        simpLib.merge_ss
          [fcpLib.FCP_ss, SIZES_ss, simpLib.rewrites rw,
           simpLib.std_conv_ss
             {conv = CHANGED_CONV FORALL_AND_CONV,
              name = "FORALL_AND_CONV",
              pats = [``!x:'a. P /\ Q:bool``]}]
  fun WORD_BIT_EQ_CONV t =
        if is_eq t orelse wordsSyntax.is_index t then
          (SIMP_CONV (std_ss++WORD_BIT_EQ_ss++BIT_ss) [SPEC `^Na` n2w_def] THENC
           TRY_CONV DECIDE_CONV) t
        else
          raise ERR "WORD_BIT_EQ_CONV" "Not a word equality"
  val WORD_BIT_EQ_ss = simpLib.named_merge_ss "word bit eq"
                         [WORD_BIT_EQ_ss, numSimps.ARITH_ss]
  fun WORD_DP_PROVE dp t = let
          val thm1 = QCONV
                      (WORD_CONV
                        THENC
                       SIMP_CONV (bool_ss++WORD_CONST_ss++WORD_UINT_MAX_ss) rw3
                        THENC
                       SIMP_CONV (std_ss++boolSimps.LET_ss++WORD_UINT_MAX_ss++
                                  WORD_w2n_ss++WORD_SUB_ss++WORD_ADD_ss) rw4
                        THENC
                       DEPTH_CONV EXISTS_WORD_CONV) t
          val t1 = rhs (concl thm1)
          val bnds = mk_bounds_thms t1
          val t2 = mk_imp (concl bnds, t1)
          val _ = if 0 < !trace_word_decide then
                    (print ("Trying to prove:\n");
                     Parse.print_term t2;
                     print "\n")
                  else
                    ()
          val thm2 = dp t2
          val conv = RAND_CONV (PURE_ONCE_REWRITE_CONV [GSYM thm1])
        in
          MP (CONV_RULE conv thm2) bnds
        end
   fun WORD_DP pre_conv dp tm =
          let fun conv t =
                if term_eq T t then
                  ALL_CONV t
                else
                  STRIP_QUANT_CONV (EQT_INTRO o (WORD_DP_PROVE dp)) t
          in
            EQT_ELIM
              ((pre_conv THENC DEPTH_CONV (WORD_BIT_EQ_CONV THENC EQ_CONV)
                         THENC DEPTH_CONV (conv THENC EQ_CONV)
                         THENC REWRITE_CONV []) tm)
          end handle UNCHANGED => raise ERR "WORD_DP" "Failed to prove goal"
   val WORD_DECIDE = WORD_DP WORD_CONV DECIDE
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
    CONV_TAC (EQT_INTRO o WORD_DECIDE)) (asl, w);

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

fun dest_word_literal t =
let val n = (rhs o concl o EVAL o mk_w2n) t in
  numLib.dest_numeral n
end handle HOL_ERR _ =>
  raise ERR "dest_word_literal" "term is not a word literal with known length";

(* ------------------------------------------------------------------------- *)

val Cases_word = Cases;
val Cases_on_word = Cases_on;

val LESS_CONV =
let val compset = reduceLib.num_compset()
    val thm = SUC_RULE prim_recTheory.LESS_THM
    val _ = add_thms [thm] compset
in
 CBV_CONV compset
end;

local
  val tac =
    POP_ASSUM (fn th => STRIP_ASSUME_TAC
               (CONV_RULE (DEPTH_CONV SIZES_CONV THENC LESS_CONV) th)) THEN
    POP_ASSUM SUBST1_TAC
in
  val Cases_word_value = Cases THEN tac
  fun Cases_on_word_value t = Cases_on t THEN tac
end;

val Induct_word =
  recInduct WORD_INDUCT
    THEN CONJ_TAC
    THENL [ALL_TAC,
      CONV_TAC (QCONV (TRY_CONV (STRIP_QUANT_CONV
                  (RATOR_CONV (DEPTH_CONV SIZES_CONV)))))
        THEN NTAC 3 STRIP_TAC];

(* ------------------------------------------------------------------------- *)

val word_pp_mode = ref 0;
val word_cast_on = ref false;

fun print_word f Gs sys (ppfns:term_pp_types.ppstream_funs) gravs d pps t = let
   open Portable term_pp_types
   val (str,brk) = (#add_string ppfns, #add_break ppfns);
   val (n,x) = dest_n2w t
   val m = fcpLib.index_to_num x handle HOL_ERR _ => Arbnum.zero
   val v = numSyntax.dest_numeral n
in
  (if !Globals.show_types orelse !word_cast_on then str "(" else ());
  str
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
     | StringCvt.HEX => "0x"^(Arbnum.toHexString v)) ^ "w");
  (if !Globals.show_types orelse !word_cast_on then
    (brk (1,2); pp_type pps (type_of t); str ")")
   else ())
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun output_words_as f = Parse.temp_add_user_printer
  ("wordsLib.print_word", ``words$n2w x : 'a word``, print_word f);

val _ = Feedback.register_trace("word printing", word_pp_mode, 4);

val _ = output_words_as
   (fn (l, v) =>
       if (!word_pp_mode = 0) andalso
          Arbnum.<=(Arbnum.fromHexString "10000", v)
       then
         StringCvt.HEX
       else if !word_pp_mode = 0 orelse !word_pp_mode = 3 then
         StringCvt.DEC
       else if !word_pp_mode = 1 then
         StringCvt.BIN
       else if !word_pp_mode = 2 then
         StringCvt.OCT
       else if !word_pp_mode = 4 then
         StringCvt.HEX
       else
         raise ERR "output_words_as" "invalid printing mode");

fun output_words_as_bin() = set_trace "word printing" 1;
fun output_words_as_dec() = set_trace "word printing" 3;
fun output_words_as_hex() = set_trace "word printing" 4;

fun output_words_as_oct() =
  (base_tokens.allow_octal_input := true; set_trace "word printing" 2);

fun remove_word_printer () =
  (Parse.remove_user_printer "wordsLib.print_word"; ())

(* ------------------------------------------------------------------------- *)
(* A pretty-printer that shows the types for ><, w2w and @@                  *)
(* ------------------------------------------------------------------------- *)

fun word_cast Gs sys (ppfns:term_pp_types.ppstream_funs) (pg,lg,rg) d pps t =
let
   open Portable term_pp_types
   val (str,brk) = (#add_string ppfns, #add_break ppfns);
   fun stype tm = String.extract(type_to_string (type_of tm),1,NONE)
   fun delim i act = case pg of
                        Prec(j,_) => if i <= j then act() else ()
                      | _ => ()
   val (f,x) = strip_comb t
in
  case (fst (dest_const f), x)
    of ("n2w",[a]) =>
          let val prec = Prec (2000,"n2w") in
            begin_block pps INCONSISTENT 0;
            delim 200 (fn () => str "(");
            trace ("types", 1) (sys (pg,lg,rg) d) f; brk (1,2);
            sys (prec,prec,prec) (d - 1) a;
            delim 200 (fn () => str ")");
            end_block pps
          end
     | ("w2w",[a]) =>
          let val prec = Prec (2000,"w2w") in
            begin_block pps INCONSISTENT 0;
            delim 200 (fn () => str "(");
            trace ("types", 1) (sys (pg,lg,rg) d) f; brk (1,2);
            sys (prec,prec,prec) (d - 1) a;
            delim 200 (fn () => str ")");
            end_block pps
          end
     | ("sw2sw",[a]) =>
          let val prec = Prec (2000,"sw2sw") in
            begin_block pps INCONSISTENT 0;
            delim 200 (fn () => str "(");
            trace ("types", 1) (sys (pg,lg,rg) d) f; brk (1,2);
            sys (prec,prec,prec) (d - 1) a;
            delim 200 (fn () => str ")");
            end_block pps
          end
     | ("word_concat",[a,b]) =>
          let val prec = Prec (2000,"word_concat") in
            begin_block pps INCONSISTENT 0;
            delim 200 (fn () => str "(");
            trace ("types", 1) (sys (pg,lg,rg) d) f; brk (1,2);
            sys (prec,prec,prec) (d - 1) a; brk (1,0);
            sys (prec,prec,prec) (d - 1) b;
            delim 200 (fn () => str ")");
            end_block pps
          end
     | ("word_extract",[h,l,a]) =>
          let val prec = Prec (2000,"word_extract") in
            begin_block pps INCONSISTENT 0;
            delim 200 (fn () => str "(");
            str "(";
            str "(";
            sys (prec,prec,prec) (d - 1) h; brk(1,2);
            str "><"; brk (1,2);
            sys (prec,prec,prec) (d - 1) l;
            str ")"; brk (1,2);
            pp_type pps (type_of (list_mk_comb (f,[h,l])));
            str ")"; brk (1,2);
            sys (prec,prec,prec) (d - 1) a;
            delim 200 (fn () => str ")");
            end_block pps
          end
     | _ => raise term_pp_types.UserPP_Failed
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun add_word_cast_printer () = (word_cast_on := true;
  Parse.temp_add_user_printer ("wordsLib.word_cast", ``f:'b word``, word_cast));

fun remove_word_cast_printer () =
  (word_cast_on := false; Parse.remove_user_printer "wordsLib.word_cast"; ());

(* ------------------------------------------------------------------------- *)
(* Guessing the word length for the result of extraction (><),               *)
(* concatenate (@@), word_replicate and concat_word_list                     *)
(* ------------------------------------------------------------------------- *)

val notify_on_word_length_guess = ref true;
val guessing_word_lengths = ref false;

val _ = Feedback.register_btrace("notify word length guesses",
                                  notify_on_word_length_guess);

val _ = Feedback.register_btrace("guess word lengths",
                                  guessing_word_lengths);

fun guess_lengths ()      = set_trace "guess word lengths" 1;
fun dont_guess_lengths () = set_trace "guess word lengths" 0;

fun t2s t = String.extract(Hol_pp.type_to_string t, 1, NONE);

fun LENGTH_INST t =
let open numSyntax
    val word_type = wordsSyntax.dest_word_type o type_of
    val ty = word_type t
in
  if Type.polymorphic ty then
    case dest_strip t
    of ("word_extract", [h,l,_]) =>
          let val nh = dest_numeral h
              val nl = dest_numeral l
              val nt = Arbnum.- (Arbnum.plus1 nh, nl)
          in
            ty |-> fcpLib.index_type nt
          end
     | ("word_concat", [a,b]) =>
          let val na = fcpLib.index_to_num (word_type a)
              val nb = fcpLib.index_to_num (word_type b)
              val nt = Arbnum.+ (na, nb)
          in
            ty |-> fcpLib.index_type nt
          end
     | ("word_replicate", [m,a]) =>
          let val nm = dest_numeral m
              val na = fcpLib.index_to_num (word_type a)
              val nt = Arbnum.* (nm, na)
          in
            ty |-> fcpLib.index_type nt
          end
     | ("concat_word_list", [l]) =>
          let val (ls,tyl) = listSyntax.dest_list l
              val nl = fcpLib.index_to_num (wordsSyntax.dest_word_type tyl)
              val nt = Arbnum.* (Arbnum.fromInt (length ls), nl)
          in
            ty |-> fcpLib.index_type nt
          end
     | _ => raise ERR "LENGTH_INST" ""
  else
    raise ERR "LENGTH_INST" ""
end;

fun inst_word_lengths tm =
  case Lib.total (HolKernel.find_term (Lib.can LENGTH_INST)) tm
  of NONE => tm
   | SOME subtm =>
       let val (theinst as {redex,residue}) = LENGTH_INST subtm
           val _ = if !Globals.interactive andalso !notify_on_word_length_guess
                   then
                     Feedback.HOL_MESG
                       (String.concat ["assigning word length: ",
                                       t2s redex, " <- ", t2s residue])
                   else
                     ()
       in
         inst_word_lengths (Term.inst [theinst] tm)
       end

fun word_post_process_term t =
  if !guessing_word_lengths then
     inst_word_lengths (fcpLib.inst_fcp_lengths t)
  else
     t;

val _ = Parse.post_process_term :=
  (word_post_process_term o !Parse.post_process_term);

val operators = [("+", "word_add"), ("-", "word_sub"),
                 ("numeric_negate", "word_2comp"),
                 ("*", "word_mul"), ("<", "word_lt"), (">", "word_gt"),
                 ("<=", "word_le"), (">=", "word_ge"), ("/", "word_sdiv")];

fun deprecate_word () =
  app (fn (opname, name) =>
         temp_send_to_back_overload opname {Name = name, Thy = "words"}
         handle HOL_ERR _ => ()) operators;

fun prefer_word () =
  app (fn (opname, name) =>
         temp_bring_to_front_overload opname {Name = name, Thy = "words"}
         handle HOL_ERR _ => ()) operators;

val _ = Defn.const_eq_ref := (!Defn.const_eq_ref ORELSEC word_EQ_CONV);

end
