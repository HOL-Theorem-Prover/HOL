(* ===================================================================== *)
(* FILE          : num_conv.sml                                          *)
(* DESCRIPTION   : num_conv maps a number constant to a theorem equating *)
(*                 it with the successor of its predecessor. Translated  *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHOR        : T.Melham                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : 87.08.23                                              *)
(*                 September 11, 1991                                    *)
(* ===================================================================== *)


structure Num_conv :> Num_conv =
struct

open HolKernel basicHol90Lib Parse Psyntax;

(* this code no longer needs to use mk_thm, because numbers are no
   longer an infinite family of constants but rather built-up in a
   binary fashion. *)

fun NUM_CONV_ERR function message =
         HOL_ERR{origin_structure ="Num_conv",
                 origin_function = function,
                 message = message}

val N = ==`:num`==
val ZERO = --`0`--
val SUC = --`SUC`--
val PRE = --`PRE`--
val bit1 = --`NUMERAL_BIT1`--
val bit2 = --`NUMERAL_BIT2`--
val eq = --`$= :num->num->bool`--
val lt_0 = --`$< 0`--

val PRE_SUC_EQ = arithmeticTheory.PRE_SUC_EQ
  (* |- !m n. 0 < n ==> ((m = PRE n) = SUC m = n) *)
val save_zero = prove(Term`NUMERAL ALT_ZERO = 0`,
                      REWRITE_TAC [arithmeticTheory.NUMERAL_DEF,
                                   arithmeticTheory.ALT_ZERO]);

val numeral_pre = numeralTheory.numeral_pre
val numeral_lt = numeralTheory.numeral_lt
val numeral_distrib = numeralTheory.numeral_distrib

fun num_CONV t =
  if is_numeral t andalso t <> ZERO then let
    val pre_t = mk_comb(PRE, t)
    val pre_thm =
      SYM (REWRITE_CONV [numeral_pre, numeral_distrib, save_zero] pre_t)
    val result_t = lhs (concl pre_thm)
    val lt_t = mk_comb(lt_0, t)
    val less_thm = EQT_ELIM (REWRITE_CONV [numeral_lt, numeral_distrib] lt_t)
    val thm0 = MP (SPECL [result_t, t] PRE_SUC_EQ) less_thm
  in
    SYM (EQ_MP thm0 pre_thm)
  end
  else raise NUM_CONV_ERR "num_CONV" "Term either not a numeral or zero"




end; (* Num_conv *)
