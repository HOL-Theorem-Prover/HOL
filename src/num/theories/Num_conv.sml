(* ===================================================================== *)
(* FILE          : num_conv.sml                                          *)
(* DESCRIPTION   : num_conv maps a number constant to a theorem equating *)
(*                 it with the successor of its predecessor.             *)
(*                                                                       *)
(* AUTHOR        : T.Melham                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : 87.08.23                                              *)
(*                 September 11, 1991                                    *)
(* REVISED       : Michael Norrish 1999, for numerals                    *)
(*                 (this code no longer needs to use mk_thm, because     *)
(*                  numbers are no longer an infinite family of          *)
(*                  constants but rather built-up in a binary fashion)   *)
(* ===================================================================== *)


structure Num_conv :> Num_conv =
struct

open HolKernel Parse boolLib Psyntax;

fun NUM_CONV_ERR function message =
         HOL_ERR{origin_structure ="Num_conv",
                 origin_function = function,
                 message = message}

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars

(* |- !m n. 0 < n ==> ((m = PRE n) = SUC m = n) *)
val PRE_SUC_EQ      = arithmeticTheory.PRE_SUC_EQ
val numeral_pre     = numeralTheory.numeral_pre
val numeral_lt      = numeralTheory.numeral_lt
val numeral_distrib = numeralTheory.numeral_distrib
val save_zero =
  prove(Term`NUMERAL ALT_ZERO = 0`,
   REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.ALT_ZERO]);


local val RW_CONV1 = REWRITE_CONV [numeral_pre, numeral_distrib, save_zero]
      val RW_CONV2 = REWRITE_CONV [numeral_lt, numeral_distrib]
      val ZERO = Term`0`
      val PRE  = Term`PRE`
      val lt_0 = Term`$< 0`
      val one = Term`1`
      val two = Term`2`
in
fun num_CONV t =
 if t=one then arithmeticTheory.ONE else
 if t=two then arithmeticTheory.TWO else
 if Numeral.is_numeral t andalso t <> ZERO
 then let val pre_t    = mk_comb(PRE, t)
          val pre_thm  = SYM (RW_CONV1 pre_t)
          val result_t = lhs (concl pre_thm)
          val less_thm = EQT_ELIM (RW_CONV2 (mk_comb(lt_0, t)))
          val thm0     = MP (SPECL [result_t, t] PRE_SUC_EQ) less_thm
      in
         SYM (EQ_MP thm0 pre_thm)
      end
 else raise NUM_CONV_ERR "num_CONV" "Term either not a numeral or zero"
end;

end; (* Num_conv *)
