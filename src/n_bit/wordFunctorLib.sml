functor wordFunctorLib (structure wordTheory : sig
  val HB_def : Thm.thm
  val WL_def : Thm.thm
  val word_0 : Thm.thm
  val word_1 : Thm.thm
  val word_L_def : Thm.thm
  val word_H_def : Thm.thm
  val word_T : Thm.thm
  val MOD_WL_EVAL : Thm.thm
  val MSBn_def : Thm.thm
  val ADD_EVAL2 : Thm.thm
  val MUL_EVAL2 : Thm.thm
  val ONE_COMP_EVAL2 : Thm.thm
  val TWO_COMP_EVAL2 : Thm.thm
  val word_sub : Thm.thm
  val AND_EVAL2 : Thm.thm
  val OR_EVAL2 : Thm.thm
  val EOR_EVAL2 : Thm.thm
  val LSL_EVAL : Thm.thm
  val LSR_THM : Thm.thm
  val ASR_THM : Thm.thm
  val ROR_THM : Thm.thm
  val RRX_EVAL2 : Thm.thm
  val WORD_BIT_def : Thm.thm
  val WORD_BITS_def : Thm.thm
  val WORD_SLICE_def : Thm.thm
  val w2n_EVAL : Thm.thm
  val n2w_11 : Thm.thm
  val MSB_EVAL2 : Thm.thm
  val LSB_EVAL2 : Thm.thm
  val LT_EVAL : Thm.thm
  val LE_EVAL : Thm.thm
  val GT_EVAL : Thm.thm
  val GE_EVAL : Thm.thm
  val LO_EVAL : Thm.thm
  val LS_EVAL : Thm.thm
  val HI_EVAL : Thm.thm
  val HS_EVAL : Thm.thm
end) : sig
  include Abbrev

  val word_compset : unit -> computeLib.compset

  val WORD_CONV    : conv
  val WORD_RULE    : thm -> thm
  val WORD_TAC     : tactic
end =
struct

open HolKernel boolLib bossLib computeLib
     arithmeticTheory bitsTheory numeral_bitsTheory wordTheory;

(* -------------------------------------------------------- *)

val THE_WL = SIMP_RULE arith_ss [HB_def,arithmeticTheory.ADD1] WL_def;

val wl = (numSyntax.dest_numeral o rhs o concl) THE_WL;

val sn = Arbnum.toString wl;

(* -------------------------------------------------------- *)

fun word_compset () =
  let val rws = reduceLib.num_compset()
      val _ = add_thms
     [numeralTheory.numeral_funpow, pairTheory.UNCURRY_DEF, LET_THM,
      LT_EVAL, LE_EVAL, GT_EVAL, GE_EVAL,
      LO_EVAL, LS_EVAL, HI_EVAL, HS_EVAL,
      THE_WL, HB_def, word_0, word_1, word_L_def, word_H_def, word_T,
      MOD_WL_EVAL, w2n_EVAL, n2w_11,
      ADD_EVAL2, MUL_EVAL2, word_sub,
      ONE_COMP_EVAL2, TWO_COMP_EVAL2,
      AND_EVAL2, OR_EVAL2, EOR_EVAL2,
      LSL_EVAL, LSR_THM, ASR_THM, ROR_THM, RRX_EVAL2,
      WORD_BIT_def, WORD_BITS_def, WORD_SLICE_def,
      MSB_EVAL2, LSB_EVAL2,
      iBITWISE, NUMERAL_BITWISE, NUMERAL_DIV2,
      DIVMOD_2EXP, iMOD_2EXP, NUMERAL_MOD_2EXP, NUMERAL_DIV_2EXP, TIMES_2EXP_def,
      MSBn_def, LSBn_def, BITV_def, SBIT_def, BITS_def, BIT_def, SLICE_def
      ] rws
in
   rws
end;

val WORD_CONV = WEAK_CBV_CONV (word_compset());
val WORD_RULE = CONV_RULE WORD_CONV;
val WORD_TAC = CONV_TAC WORD_CONV;

fun odd n = Arbnum.mod2 n = Arbnum.one;

fun pow(a,b) = if odd b then Arbnum.*(a,pow(a,Arbnum.less1 b))
               else if b = Arbnum.zero then Arbnum.one
               else pow(Arbnum.*(a,a),Arbnum.div2 b);

val max = pow(Arbnum.fromInt 2,wl);

local
  val base = Arbnum.fromInt 16
  fun to_hex_char n = let
      val p = Arbnum.toInt (Arbnum.mod(n,base))
    in
      str (if p < 10 then chr (ord #"0" + p) else chr (ord #"A" + p - 10))
    end
  fun to_hex_string n = let
      val s = to_hex_char n
    in
      if Arbnum.<(n,base) then s else to_hex_string (Arbnum.div(n,base))^s
    end
in
  fun num_to_hex n = "0x"^to_hex_string n
end;

fun word_n_print sys gravs d pps t = let
   open Portable term_pp_types
   val (l,r) = dest_comb t
   val n = numSyntax.dest_numeral r
   val m = Arbnum.mod(n,max)
in
  if l = Term `n2w` then
    add_string pps (num_to_hex m)
  else
    raise UserPP_Failed
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _ = Parse.temp_add_user_printer ({Tyop = "word"^sn, Thy = "word"^sn}, word_n_print);

(* -------------------------------------------------------- *)

end
