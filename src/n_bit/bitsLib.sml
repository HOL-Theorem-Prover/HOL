structure bitsLib :> bitsLib =
struct

(* app load ["bitsTheory","numeral_bitsTheory]; *)

open HolKernel Parse boolLib bossLib Q computeLib
     arithmeticTheory bitsTheory numeral_bitsTheory;

(* -------------------------------------------------------- *)

fun NUMERAL_ONLY_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss l o Q.INST [n |-> `0`]) y)
          ((GEN_ALL o Q.INST [n |-> `NUMERAL n`]) y)
  end;

(*
local
  val _ = set_trace "metis" 0
in
  val log2_thm =  prove(
    `!x q r. LOG2 x = let p = 2 ** q in
               if (x = p + r) /\ (r < p) then q else LOG2 x`,
    RW_TAC (std_ss++boolSimps.LET_ss) []
      THEN METIS_TAC [LOG2_UNIQUE]
  )
end;

val dest_log2 = dest_monop ``$LOG2`` (mk_HOL_ERR "bitsLib" "dest_log2" "");

fun cbv_LOG2_CONV tm =
 let open Arbnum numSyntax
     val x = dest_log2 tm
     val n = dest_numeral x
     val q = log2 n
     val r = n mod pow(two, q)
 in Drule.SPECL [x, mk_numeral q, mk_numeral r] log2_thm
 end
 handle HOL_ERR _ => raise (mk_HOL_ERR "bitsLib" "cbv_LOG2" "")
      | Domain => raise (mk_HOL_ERR "bitsLib" "cbv_LOG2" "")
*)

fun bits_compset () =
  let val compset = reduceLib.num_compset()
      val _ = add_thms
                [numeralTheory.numeral_funpow, pairTheory.UNCURRY_DEF,
                 iBITWISE, NUMERAL_BITWISE, NUMERAL_DIV2, SIGN_EXTEND_def,
                 DIVMOD_2EXP, iMOD_2EXP, NUMERAL_MOD_2EXP, NUMERAL_DIV_2EXP, TIMES_2EXP_def,
                 LSBn_def, BITV_def, SBIT_def,
                 NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` BITS_def,
                 NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` SLICE_def,
                 NUMERAL_ONLY_RULE [BITS_ZERO2] `n`  BIT_def,
                 numeral_log2,numeral_ilog2
                 ] compset
   (*   val _ = add_conv (``$LOG2``, 1, cbv_LOG2_CONV) compset *)
in
  compset
end;

val BITS_CONV = CBV_CONV (bits_compset());
val BITS_RULE = CONV_RULE BITS_CONV;
val BITS_TAC = CONV_TAC BITS_CONV;

end
