(* ===================================================================== *)
(* FILE          : Num_conv.sml                                          *)
(* DESCRIPTION   : num_CONV maps a numeric literal to a theorem equating *)
(*                 it with the successor of its predecessor.             *)
(*                                                                       *)
(* AUTHOR        : T.Melham                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : 87.08.23                                              *)
(*                 September 11, 1991                                    *)
(* REVISED       : Michael Norrish 1999, for numerals                    *)
(*                 (this code formerly used mk_thm, but no longer:       *)
(*                  numbers are built-up in a binary fashion)            *)
(* ===================================================================== *)


structure Num_conv :> Num_conv =
struct

open HolKernel Parse boolLib;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars

(* |- !m n. 0 < n ==> ((m = PRE n) = SUC m = n) *)

val PRE_SUC_EQ      = arithmeticTheory.PRE_SUC_EQ

val numeral_pre     = numeralTheory.numeral_pre
val numeral_lt      = numeralTheory.numeral_lt
val numeral_distrib = numeralTheory.numeral_distrib
val save_zero =
  prove(Term`NUMERAL ZERO = 0`,
   REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.ALT_ZERO]);


local val RW_CONV1 = REWRITE_CONV [numeral_pre, numeral_distrib, save_zero]
      val RW_CONV2 = REWRITE_CONV [numeral_lt, numeral_distrib]
      val ZERO = numSyntax.zero_tm
      val PRE  = numSyntax.pre_tm
      val lt_0 = mk_comb(numSyntax.less_tm, ZERO)
      val one  = numSyntax.mk_numeral(Arbnum.fromInt 1)
      val two  = numSyntax.mk_numeral(Arbnum.fromInt 2)
in
fun num_CONV t =
 if aconv t one then arithmeticTheory.ONE else
 if aconv t two then arithmeticTheory.TWO else
 if Literal.is_numeral t andalso not (aconv t ZERO)
 then let val pre_t    = mk_comb(PRE, t)
          val pre_thm  = SYM (RW_CONV1 pre_t)
          val result_t = lhs (concl pre_thm)
          val less_thm = EQT_ELIM (RW_CONV2 (mk_comb(lt_0, t)))
          val thm0     = MP (SPECL [result_t, t] PRE_SUC_EQ) less_thm
      in
         SYM (EQ_MP thm0 pre_thm)
      end
 else raise (mk_HOL_ERR "Num_conv" "num_CONV"
                        "Term either not a numeral or zero")
end;

end; (* Num_conv *)
