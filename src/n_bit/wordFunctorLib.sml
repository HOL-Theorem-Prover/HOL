functor wordFunctorLib (structure wordTheory : sig
  type thm = Thm.thm
  val HB_def : thm
  val WL_def : thm
  val word_0 : thm
  val word_1 : thm
  val word_L_def : thm
  val word_H_def : thm
  val word_T : thm
  val MOD_WL_def : thm
  val MSBn_def : thm
  val ADD_EVAL2 : thm
  val MUL_EVAL2 : thm
  val ONE_COMP_def : thm
  val TWO_COMP_def : thm
  val ONE_COMP_EVAL : thm
  val TWO_COMP_EVAL : thm
  val word_sub : thm
  val AND_def : thm
  val OR_def : thm
  val EOR_def : thm
  val AND_EVAL : thm
  val OR_EVAL : thm
  val EOR_EVAL : thm
  val LSL_EVAL : thm
  val LSR_THM : thm
  val ASR_THM : thm
  val ROR_THM : thm
  val RRX_EVAL : thm
  val RRXn_def : thm
  val LSR_ONE_def : thm
  val WORD_BIT_def : thm
  val WORD_BITS_def : thm
  val WORD_SLICE_def : thm
  val w2n_EVAL : thm
  val n2w_11 : thm
  val MSB_EVAL : thm
  val LSB_EVAL2 : thm
  val LT_EVAL : thm
  val LE_EVAL : thm
  val GT_EVAL : thm
  val GE_EVAL : thm
  val LO_EVAL : thm
  val LS_EVAL : thm
  val HI_EVAL : thm
  val HS_EVAL : thm
  val FORALL_WORD : thm
  val EQUIV_def : thm
  val ONE_COMP_THM : thm
  val BITWISE_THM2 : thm
  val ONE_COMP_BITWISE_THM : thm
end) : sig
  include Abbrev

  val word_compset : unit -> computeLib.compset

  val WORD_CONV    : conv
  val WORD_RULE    : thm -> thm
  val WORD_TAC     : tactic

  val NORM_TAC     : tactic
  val WORD_EQ_TAC  : tactic

  val pp_word_signed_bin   : unit -> unit
  val pp_word_signed_oct   : unit -> unit
  val pp_word_signed_dec   : unit -> unit
  val pp_word_signed_hex   : unit -> unit
  val pp_word_unsigned_bin : unit -> unit
  val pp_word_unsigned_oct : unit -> unit
  val pp_word_unsigned_hex : unit -> unit
  val pp_word_off  : unit -> term_pp_types.userprinter option
end =
struct

open HolKernel boolLib bossLib computeLib
     arithmeticTheory bitsTheory numeral_bitsTheory wordTheory;

(* -------------------------------------------------------- *)

val THE_WL = SIMP_RULE arith_ss [HB_def,arithmeticTheory.ADD1] WL_def;
val MOD_WL_EVAL = REWRITE_RULE [THE_WL,GSYM MOD_2EXP_def] MOD_WL_def;

val RRX_EVAL2 = GEN_ALL (REWRITE_RULE [GSYM DIV2_def,RRXn_def,LSR_ONE_def,HB_def] RRX_EVAL);

val MSB_EVAL2 = GEN_ALL (REWRITE_RULE [MSBn_def,HB_def] MSB_EVAL);

val ONE_COMP_EVAL2 = GEN_ALL (SIMP_RULE arith_ss [ONE_COMP_def,THE_WL] ONE_COMP_EVAL);
val TWO_COMP_EVAL2 = GEN_ALL (SIMP_RULE arith_ss [TWO_COMP_def,THE_WL] TWO_COMP_EVAL);

val OR_EVAL2 = GEN_ALL (SIMP_RULE bool_ss [OR_def,THE_WL] OR_EVAL);
val AND_EVAL2 = GEN_ALL (SIMP_RULE bool_ss [AND_def,THE_WL] AND_EVAL);
val EOR_EVAL2 = GEN_ALL (SIMP_RULE bool_ss [EOR_def,THE_WL] EOR_EVAL);

val LT_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] LT_EVAL;
val LE_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] LE_EVAL;
val GT_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] GT_EVAL;
val GE_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] GE_EVAL;
val LO_EVAL = REWRITE_RULE [MOD_WL_EVAL] LO_EVAL;
val LS_EVAL = REWRITE_RULE [MOD_WL_EVAL] LS_EVAL;
val HI_EVAL = REWRITE_RULE [MOD_WL_EVAL] HI_EVAL;
val HS_EVAL = REWRITE_RULE [MOD_WL_EVAL] HS_EVAL;

(* -------------------------------------------------------- *)

fun NUMERAL_ONLY_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss l o Q.INST [n |-> `0`]) y)
          ((GEN_ALL o Q.INST [n |-> `NUMERAL n`]) y)
  end;

(* -------------------------------------------------------- *)

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
      iBITWISE, NUMERAL_BITWISE, NUMERAL_DIV2, SIGN_EXTEND_def,
      DIVMOD_2EXP, iMOD_2EXP, NUMERAL_MOD_2EXP, NUMERAL_DIV_2EXP, TIMES_2EXP_def,
      MSBn_def, LSBn_def, BITV_def, SBIT_def,
      NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` BITS_def,
      NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` SLICE_def,
      NUMERAL_ONLY_RULE [BITS_ZERO2] `n`  BIT_def
      ] rws
in
   rws
end;

val WORD_CONV = CBV_CONV (word_compset());
val WORD_RULE = CONV_RULE WORD_CONV;
val WORD_TAC = CONV_TAC WORD_CONV;

val thyname = "word"^sn;
val n2w_term =
  mk_thy_const {Name = "n2w", Thy = thyname,
                Ty = mk_thy_type {Tyop = "num", Thy = "num", Args = []} -->
                     mk_thy_type {Tyop = thyname, Thy = thyname, Args = []}};

datatype nbase = binary | octal | decimal | hexadecimal;

fun word_n_print tc base sys gravs d pps t = let
   open Portable term_pp_types
   val (l,r) = dest_comb t
   val n = numSyntax.dest_numeral r
   val exph = Arbnum.pow(Arbnum.two,Arbnum.less1 wl)
   val expl = Arbnum.*(Arbnum.two,exph)
   val un = Arbnum.mod(n,expl)
   val neg = tc andalso Arbnum.div(n,exph) = Arbnum.one
   val sn = if neg then Arbnum.-(expl,un) else un
in
  if l = n2w_term then
    add_string pps
      ((if neg then "~" else "")^
       (case base of
          decimal     => (Arbnum.toString sn)
        | binary      => "0b"^(Arbnum.toBinString sn)
        | octal       => "0" ^(Arbnum.toOctString sn)
        | hexadecimal => "0x"^(Arbnum.toHexString sn))^"w")
  else
    raise UserPP_Failed
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun pp_word tc base =
   Parse.temp_add_user_printer ({Tyop = thyname, Thy = thyname}, word_n_print tc base);

fun pp_word_signed_bin() = pp_word true binary;
fun pp_word_signed_oct() = pp_word true octal;
fun pp_word_signed_dec() = pp_word true decimal;
fun pp_word_signed_hex() = pp_word true hexadecimal;
fun pp_word_unsigned_bin() = pp_word false binary;
fun pp_word_unsigned_oct() = pp_word false octal;
fun pp_word_unsigned_hex() = pp_word false hexadecimal;

fun pp_word_off() = Parse.remove_user_printer ({Tyop = thyname, Thy = thyname});

(* -------------------------------------------------------- *)

(*---------------------------------------------------------------------------*)
(* NORM_TAC : normalize goals of the form                                    *)
(*                                                                           *)
(*    !w1 ... wn. M = N                                                      *)
(*                                                                           *)
(* where M and N are built from AND, OR, EOR, and NOT. In most cases,        *)
(* should reduce to a boolean expression suitable for a decision procedure.  *)
(*---------------------------------------------------------------------------*)

val NORM_TAC =
 SIMP_TAC std_ss [FORALL_WORD] THEN
 SIMP_TAC std_ss [ONE_COMP_EVAL, AND_EVAL, OR_EVAL, EOR_EVAL] THEN
 SIMP_TAC std_ss [n2w_11,GSYM EQUIV_def] THEN
 RW_TAC bool_ss [EOR_def, AND_def, OR_def, 
                 ONE_COMP_BITWISE_THM, GSYM BITWISE_THM2, BITWISE_THM];

val WORD_EQ_TAC = NORM_TAC THEN tautLib.TAUT_TAC;


end
