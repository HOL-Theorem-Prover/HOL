open HolKernel boolLib bossLib Parse;
open EmitML wordsTheory;
open fcp_emitTheory bit_emitTheory;

val _ = new_theory "words_emit";

val word_index_def = Define `word_index (w:'a word) n = w ' n`;
val w2w_itself_def = Define `w2w_itself (:'a) w = (w2w w): 'a word`;
val sw2sw_itself_def = Define `sw2sw_itself (:'a) w = (sw2sw w): 'a word`;
val word_eq_def = Define `word_eq (v: 'a word) w = (v = w)`;

val word_extract_itself_def = Define`
  word_extract_itself (:'a) h l w = (word_extract h l w): bool ** 'a`;

val word_concat_itself_def = Define`
  word_concat_itself (:'a) v w = (word_concat v w): bool ** 'a`;

val fromNum_def = Define`
  fromNum (n, (:'a)) = n2w_itself (n MOD dimword (:'a),(:'a))`;

val _ = ConstMapML.insert_cons ``n2w_itself``;

fun mk_index i =
  let val n = Arbnum.fromInt i
      val x = Int.toString i
      val typ = fcpLib.index_type n
      val s = String.extract(with_flag (type_pp.pp_num_types, false)
                 type_to_string typ, 1, NONE)
      val w = "type word" ^ x ^ " = " ^ s ^ " word"
      val a = "fun toWord" ^ x ^
                 " n = fromNum (n,ITSELF(numML.fromInt " ^ x ^ "))"
      val b = "val toWord" ^ x ^ " : numML.num -> word" ^ x
      val c = "val fromString" ^ x ^
                 " = o(toWord" ^ x ^ ", numML.fromString) : string -> word" ^ x
      val d = "val fromString" ^ x ^ " : string -> word" ^ x
  in
    [EmitML.MLSTRUCT w, EmitML.MLSIG w,
     EmitML.MLSTRUCT a, EmitML.MLSIG b,
     EmitML.MLSTRUCT c, EmitML.MLSIG d]
  end;

val sizes = [1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 28, 30, 32, 64]

val ALPHA_BETA_RULE = GEN_ALL o Q.INST [`a` |-> `m`, `b` |-> `n`] o SPEC_ALL

val MOD_WL =
    (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))))

val TIMES_2EXP1 =
    (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
     Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def

val word_reduce = Q.prove(
  `!b. $FCP (K b) = n2w (if b then 1 else 0) : 1 word`,
  SRW_TAC [fcpLib.FCP_ss]
     [word_index, DECIDE ``x < 1 = (x = 0n)``, fcpTheory.index_one,
      bitTheory.BITS_THM, bitTheory.BIT_def]);

val bit_field_insert = Q.prove(
  `!h l a.
     bit_field_insert h l a w =
       word_modify
         (\i b. if l <= i /\ i <= h then word_index a (i - l) else b) w`,
  SRW_TAC [fcpLib.FCP_ss]
    [word_index_def, bit_field_insert_def, word_modify_def]);

val n2w_w2n_RULE = REWRITE_RULE [n2w_w2n] o Q.SPEC `w2n w`
val word_eq_n2w = REWRITE_RULE [n2w_11] (Q.SPECL [`n2w m`,`n2w n`] word_eq_def)
val word_reduce_n2w = REWRITE_RULE [word_reduce] word_reduce_n2w
val word_eq_n2w = n2w_w2n_RULE (GEN_ALL word_eq_n2w)
val word_or_n2w = n2w_w2n_RULE word_or_n2w
val word_and_n2w = n2w_w2n_RULE word_and_n2w
val word_xor_n2w = n2w_w2n_RULE word_xor_n2w
val word_nor_n2w = n2w_w2n_RULE word_nor_n2w
val word_nand_n2w = n2w_w2n_RULE word_nand_n2w
val word_xnor_n2w = n2w_w2n_RULE word_xnor_n2w
val word_add_n2w = n2w_w2n_RULE word_add_n2w
val word_mul_n2w = n2w_w2n_RULE word_mul_n2w
val word_ge_n2w = n2w_w2n_RULE word_ge_n2w
val word_gt_n2w = n2w_w2n_RULE word_gt_n2w
val word_hi_n2w = n2w_w2n_RULE word_hi_n2w
val word_hs_n2w = n2w_w2n_RULE word_hs_n2w
val word_le_n2w = n2w_w2n_RULE word_le_n2w
val word_lo_n2w = n2w_w2n_RULE word_lo_n2w
val word_ls_n2w = n2w_w2n_RULE word_ls_n2w
val word_lt_n2w = n2w_w2n_RULE word_lt_n2w
val word_join_n2w = Q.SPECL [`n2w m`,`n2w n`] word_join_def
val word_div_n2w = Q.SPEC `n2w m` word_div_def
val word_asr_n2w = Q.SPECL [`n`,`n2w m`] word_asr_n2w
val word_lsr_n2w = Q.SPEC `n2w m` word_lsr_n2w
val word_rol_n2w = Q.SPEC `n2w m` word_rol_def
val reduce_and_n2w = Q.SPEC `n2w m` reduce_and
val reduce_or_n2w = Q.SPEC `n2w m` reduce_or
val sw2sw_n2w = Q.SPEC `n2w n` sw2sw_def
val add_with_carry_n2w = Q.SPEC `n2w n` add_with_carry_def
val reduce_xnor = ONCE_REWRITE_RULE [METIS_PROVE [] ``(<=>) = (\x y. x = y)``]
                   reduce_xnor_def

val f =
  map (DEFN o REWRITE_RULE
         [GSYM n2w_itself_def, GSYM w2w_itself_def,
          GSYM sw2sw_itself_def, GSYM word_concat_itself_def,
          GSYM word_extract_itself_def, word_T_def, word_L_def, word_H_def,
          TIMES_2EXP1, FUN_EQ_THM] o ALPHA_BETA_RULE)

val defs =
    f [dimword_def, fromNum_def] @ List.concat (map mk_index sizes) @
    f [INT_MIN_def, UINT_MAX_def, INT_MAX_def,
       w2n_n2w, word_eq_n2w, w2w_n2w, word_or_n2w, word_lsl_n2w,
       word_bits_n2w, word_signed_bits_n2w, Q.SPEC `c` word_bit_n2w,
       word_join_n2w, sw2sw_n2w, word_extract_n2w, word_slice_n2w,
       word_concat_def, word_log2_n2w, word_reverse_n2w, word_modify_n2w,
       word_lsb_n2w, word_msb_n2w, add_with_carry_n2w,
       word_1comp_n2w, word_and_n2w, word_xor_n2w,
       word_2comp_n2w, word_div_n2w, word_sdiv_def,
       MOD_WL word_add_n2w, word_sub_def, MOD_WL word_mul_n2w,
       word_lsr_n2w, word_asr_n2w, word_ror_n2w, word_rol_n2w,
       word_rrx_n2w, REWRITE_RULE [GSYM word_index_def] word_index_n2w,
       word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
       word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w,
       word_reduce_n2w, reduce_and_n2w, reduce_or_n2w, reduce_xor_def,
       reduce_xnor, reduce_nand_def, reduce_nor_def, bit_field_insert,
       w2l_def,w2s_def,
       word_to_bin_list_def,word_to_oct_list_def,
       word_to_dec_list_def,word_to_hex_list_def,
       word_to_bin_string_def,word_to_oct_string_def,
       word_to_dec_string_def,word_to_hex_string_def]

val _ = eSML "words"
  (OPEN ["sum", "num", "fcp", "bit"]
   :: MLSIG "type ('a, 'b) sum = ('a, 'b) sumML.sum"
   :: MLSIG "type 'a itself = 'a fcpML.itself"
   :: MLSIG "type 'a bit0 = 'a fcpML.bit0"
   :: MLSIG "type 'a bit1 = 'a fcpML.bit1"
   :: MLSIG "type num = numML.num"
   :: MLSIG "datatype 'a word = n2w_itself of num * 'a itself"
   :: MLSTRUCT "datatype 'a word = n2w_itself of num * 'a itself"
   :: defs)

val _ = eCAML "words"
  (MLSIGSTRUCT
     ["type num = NumML.num",
      "type ('a, 'b) sum = ('a, 'b) SumML.sum",
      "type 'a itself = 'a FcpML.itself",
      "type 'a bit0 = 'a FcpML.bit0",
      "type 'a bit1 = 'a FcpML.bit1", "",
      "type 'a word = N2w_itself of num * 'a itself"] @
   OPEN ["sum", "num", "fcp", "bit"] ::
   defs)

fun adjoin_to_theory_struct l = adjoin_to_theory {sig_ps = NONE,
  struct_ps = SOME (fn ppstrm =>
    app (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm)) l)};

val _ = adjoin_to_theory_struct
 ["val _ = ConstMapML.insert_cons(\
  \Term.prim_mk_const{Name=\"n2w_itself\",Thy=\"words\"});"];

val _ = adjoin_to_theory
 {sig_ps = SOME (fn ppstrm =>
             (PP.add_string ppstrm "val WORDS_EMIT_RULE : thm -> thm";
              PP.add_newline ppstrm)),
  struct_ps = SOME (fn ppstrm =>
   let val S = PP.add_string ppstrm
       fun NL() = PP.add_newline ppstrm
   in
     S "open HolKernel boolLib wordsTheory fcp_emitTheory;"; NL();
     S "val RHS_REWRITE_RULE = GEN_REWRITE_RULE (DEPTH_CONV o RAND_CONV) empty_rewrites";
     NL();
     S "val WORDS_EMIT_RULE = "; NL();
     S " BETA_RULE o PURE_REWRITE_RULE "; NL();
     S " ([BIT_UPDATE, fcp_n2w, word_T_def, word_L_def, word_H_def, literal_case_THM]"; NL();
     S "  @"; NL();
     S "  map GSYM [word_index_def, n2w_itself_def, w2w_itself_def, sw2sw_itself_def,"; NL();
     S "            word_concat_itself_def, word_extract_itself_def,"; NL();
     S "            FCPi_def, mk_fcp_def, literal_case_DEF]) "; NL();
     S " o RHS_REWRITE_RULE [GSYM word_eq_def];"; NL();
     NL();
     S "val _ = EmitML.reshape_thm_hook := (WORDS_EMIT_RULE o !EmitML.reshape_thm_hook);";
     NL(); NL()
   end)}

val _ = export_theory ();
