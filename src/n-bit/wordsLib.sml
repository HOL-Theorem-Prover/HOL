structure wordsLib :> wordsLib =
struct

(* interactive use:
  app load ["fcpLib", "numeral_bitTheory", "wordsTheory", "wordsSyntax"];
*)

open HolKernel Parse boolLib bossLib computeLib;
open bitTheory numeral_bitTheory wordsTheory wordsSyntax;

(* ------------------------------------------------------------------------- *)

fun is_fcp_thm s =
  String.isPrefix "finite_" s orelse String.isPrefix "dimindex_" s orelse
  String.isPrefix "dimword_" s orelse String.isPrefix "INT_MIN_"s;

val machine_sizes = (map snd o filter (is_fcp_thm o fst) o theorems) "words";

val SIZES_ss = rewrites machine_sizes;

val sizes_comp = new_compset machine_sizes;

fun SIZES_CONV t = CHANGED_CONV (CBV_CONV sizes_comp) t
  handle HOL_ERR _ =>
    let val x = (PURE_REWRITE_CONV [INT_MIN_def, dimword_IS_TWICE_INT_MIN]
                   THENC fcpLib.INDEX_CONV) t
        val _ = add_thms [x] sizes_comp
    in
      x
    end;

fun NUM_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ
     ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss l o Q.INST [n |-> `0`]) y)
     ((GEN_ALL o Q.INST [n |-> `NUMERAL n`]) y)
  end;

val MOD_WL = 
  (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))));

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
   n2w_11, n2w_w2n, w2n_n2w, w2w_def, sw2sw_def, word_len_def,
   word_L_def, word_H_def, word_T_def,
   word_join_def, word_concat_def,
   word_reverse_n2w, word_modify_n2w, word_log2_n2w,
   word_1comp_n2w, word_or_n2w, word_xor_n2w, word_and_n2w,
   word_2comp_n2w, word_sub_def, word_div_def, word_sdiv_def,
   MOD_WL word_add_n2w, MOD_WL word_mul_n2w,
   word_asr_n2w, word_lsr_n2w, word_lsl_n2w,
   (List.last o CONJUNCTS) SHIFT_ZERO, SPEC ``NUMERAL n`` word_ror_n2w,
   word_rol_def, word_rrx_n2w,
   word_lsb_n2w, word_msb_n2w, word_bit_n2w, word_index_n2w,
   word_bits_n2w, word_slice_n2w, fcp_n2w,
   SIMP_RULE std_ss [FUN_EQ_THM] word_extract_def,
   word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
   word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w];

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

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

val WORDS_CONV = CBV_CONV (words_compset());
val WORDS_RULE = CONV_RULE WORDS_CONV;
val WORDS_TAC = CONV_TAC WORDS_CONV;

(* ------------------------------------------------------------------------- *)

val RHS_REWRITE_RULE =
  GEN_REWRITE_RULE (DEPTH_CONV o RAND_CONV) empty_rewrites;

val WORDS_EMIT_RULE =
  BETA_RULE o PURE_REWRITE_RULE ([literal_case_THM] @ (map GSYM
    [word_index_def, n2w_itself_def, w2w_itself_def, sw2sw_itself_def,
     word_concat_itself_def, word_extract_itself_def,
     fcpTheory.FCPi_def, fcpTheory.mk_fcp_def])) o
  RHS_REWRITE_RULE [GSYM word_eq_def];

(* ------------------------------------------------------------------------- *)

fun Cases_on_word tm =
   Q.ISPEC_THEN tm FULL_STRUCT_CASES_TAC ranged_word_nchotomy;

fun Cases_word (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_word" "not a forall")
  in (STRIP_TAC THEN STRUCT_CASES_TAC (Drule.ISPEC Bvar ranged_word_nchotomy)) g
  end;

(* ------------------------------------------------------------------------- *)

fun print_word base_map sys gravs d pps t = let
   open Portable term_pp_types
   val (n,x) = dest_n2w t
   val m = numSyntax.dest_numeral n
in
  add_string pps
   ((case base_map x of
       StringCvt.DEC => Arbnum.toString m
     | StringCvt.BIN => "0b"^(Arbnum.toBinString m)
     | StringCvt.OCT => "0" ^(Arbnum.toOctString m)
     | StringCvt.HEX => "0x"^(Arbnum.toHexString m)) ^ "w")
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun pp_word base_map = Parse.temp_add_user_printer
  ({Tyop = "cart", Thy = "fcp"}, print_word base_map);

fun pp_word_bin() = pp_word (fn x => StringCvt.BIN);
fun pp_word_oct() = pp_word (fn x => StringCvt.OCT);
fun pp_word_hex() = pp_word (fn x => StringCvt.HEX);

fun pp_word_dec() = Parse.remove_user_printer {Tyop="cart", Thy="fcp"};

(* Example:
val _ = pp_word (fn x => if Type.compare(x,``:i32``) = EQUAL then
                           StringCvt.HEX else StringCvt.DEC);       *)

(* ------------------------------------------------------------------------- *)
(* Guessing the word length for the result of extraction (><) and            *)
(* concatenate (@@)                                                          *)
(* ------------------------------------------------------------------------- *)

val extract_tm = ``(a >< b) :'a word -> 'b word``;

fun type_to_name t = String.extract(Hol_pp.type_to_string t, 1, NONE);

fun numeric_type_to_num t =
let val pp_n = !type_pp.pp_num_types
    val _ = type_pp.pp_num_types := true
in
  Arbnum.fromString (type_to_name t) before
  type_pp.pp_num_types := pp_n
end;

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
      let val ty = type_of t in
        case dest_type ty of
           ("fun", [x, y]) =>
              (let val fv = hd (type_vars y)
                   val na = numSyntax.dest_numeral (#residue a)
                   val nb = numSyntax.dest_numeral (#residue b)
                   val n = Arbnum.-(Arbnum.plus1 na, nb)
               in
                 if n = Arbnum.zero then [] else [word_extract (n, fv)]
               end handle _ => [])
        | _ => []
      end
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
                       numeric_type_to_num a
            val nb = if Type.is_vartype b then
                       find(vmap, b)
                     else
                     numeric_type_to_num b
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

fun guess_to_string {redex = a, residue = b} =
  type_to_name a ^ " <- " ^ type_to_name b;

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

fun guess_lengths () =
  Parse.post_process_term := (guess_word_lengths o !Parse.post_process_term);

end
