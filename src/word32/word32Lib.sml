structure word32Lib :> word32Lib =
struct

(* app load ["bossLib","bitsTheory","word32Theory"]; *)

open HolKernel boolLib computeLib bossLib 
     simpLib numLib bitsTheory word32Theory;


(* -------------------------------------------------------- *)

val word_compset =
  let val rws = reduceLib.num_compset()
      val _ = add_thms 
     [SIMP_RULE arith_ss [HB_def,arithmeticTheory.ADD1] WL_def,
      w_0,w_1,w_T,HB_def,
      MODw_EVAL,
      ADD_EVAL2,
      MUL_EVAL2,
      REDUCE_RULE ONE_COMP_EVAL2,
      REDUCE_RULE TWO_COMP_EVAL2,
      word_sub,
      BITWISE_EVAL2,
      AND_EVAL2,
      OR_EVAL2,
      EOR_EVAL2,
      word_lsl,
      LSR_EVAL,
      ASR_THM,
      ROR_THM,
      REDUCE_RULE RRX_EVAL2,
      BITw_def,
      BITSw_def,
      SLICEw_def,
      w2n_EVAL,
      MSB_EVAL2,
      LSB_EVAL2,
      numeralTheory.numeral_funpow,
      pairTheory.UNCURRY_DEF,
      TIMES_2EXP_def,DIV_2EXP_def,MOD_2EXP_def,DIVMOD_2EXP_def,
      MSBn_def,SBIT_def,BITS_THM,BIT_def,SLICE_def,LET_THM] rws
in
   rws
end;

val WORD_CONV = CBV_CONV word_compset;
val WORD_RULE = CONV_RULE WORD_CONV;
val WORD_TAC = CONV_TAC WORD_CONV;

val WORD32_CONV = WORD_CONV
val WORD32_RULE = WORD_RULE
val WORD32_TAC = WORD_TAC

local
  val base = Arbnum.fromInt 16
  fun to_hex_char n = let
      val p = Arbnum.toInt (Arbnum.mod(n,base))
    in
      str (if p < 10 then chr (ord #"0" + p) else chr (ord #"a" + p - 10))
    end
  fun to_hex_string n = let
      val s = to_hex_char n
    in
      if Arbnum.<(n,base) then s else to_hex_string (Arbnum.div(n,base))^s
    end
in
  fun num_to_hex n = "0x"^to_hex_string n
end;
 
fun word32print sys gravs d pps t = let
   open Portable term_pp_types
   val (l,r) = dest_comb t
   val n = numSyntax.dest_numeral r
   val m = Arbnum.mod(n,Arbnum.fromString "4294967296")
in
  if l = Term `n2w` then
    add_string pps (num_to_hex m)
  else
    raise UserPP_Failed
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;
 
val _ = Parse.temp_add_user_printer ({Tyop = "word32", Thy = "word32"}, word32print);

(* -------------------------------------------------------- *)

end
