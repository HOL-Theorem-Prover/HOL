(*****************************************************************************)
(* FILE          : thm_convs.sml                                             *)
(* DESCRIPTION   : Conversions for rewriting with arithmetic theorems.       *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 5th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 13th August 1996                                          *)
(*****************************************************************************)

structure DecisionArithConvs :> DecisionArithConvs =
struct

open DecisionTheorems HolKernel Parse boolTheory Drule Conv Rewrite;
infix ORELSEC |->;

type conv = Abbrev.conv

val dense = false;
val num = Type`:num`;

val m = --`m:num`--
and n = --`n:num`--
and p = --`p:num`--;

(*===========================================================================*)
(* Conversions for rewriting arithmetic terms                                *)
(*===========================================================================*)

val ADD_ASSOC_CONV = REWR_CONV (arithmeticTheory.ADD_ASSOC);

val ADD_SYM_CONV = REWR_CONV (arithmeticTheory.ADD_SYM);

val GATHER_BOTH_CONV =
 REWR_CONV
  (SYM
    (SPECL [--`a:num`--,--`b:num`--,--`x:num`--] 
           arithmeticTheory.RIGHT_ADD_DISTRIB));

val GATHER_LEFT_CONV =
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL [--`x:num`--,n] 
        arithmeticTheory.MULT_CLAUSES))]
    (SYM (SPECL [--`a:num`--,--`1`--,--`x:num`--] 
                arithmeticTheory.RIGHT_ADD_DISTRIB)));

val GATHER_NEITHER_CONV = REWR_CONV (GSYM arithmeticTheory.TIMES2);

val GATHER_RIGHT_CONV =
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL [--`x:num`--,n] 
        arithmeticTheory.MULT_CLAUSES))]
    (SYM (SPECL [--`1`--,--`b:num`--,--`x:num`--] 
                arithmeticTheory.RIGHT_ADD_DISTRIB)));

val GEQ_NORM_CONV = REWR_CONV arithmeticTheory.GREATER_EQ;

val GREAT_NORM_CONV =
   if dense
   then REWR_CONV arithmeticTheory.GREATER_DEF
   else REWR_CONV
         (SUBS [SYM (SPECL [m,n] arithmeticTheory.GREATER_DEF),
                SPEC n arithmeticTheory.SUC_ONE_ADD]
           (SPECL [n,m] arithmeticTheory.LESS_EQ));

val LEFT_ADD_DISTRIB_CONV = REWR_CONV arithmeticTheory.LEFT_ADD_DISTRIB;

val LESS_NORM_CONV =
   if dense
   then ALL_CONV
   else REWR_CONV
         (SUBS [SPEC m arithmeticTheory.SUC_ONE_ADD] 
               (SPECL [m,n] arithmeticTheory.LESS_EQ));

val MULT_ASSOC_CONV = REWR_CONV arithmeticTheory.MULT_ASSOC;

val MULT_COMM_CONV = REWR_CONV MULT_COMM;

val NOT_GEQ_NORM_CONV =
   if dense
   then REWR_CONV (TRANS (SPECL [m,n] arithmeticTheory.NOT_GREATER_EQ)
                         (SYM (SPECL [m,n] arithmeticTheory.LESS_EQ)))
   else REWR_CONV
         (SUBS [SPEC m arithmeticTheory.SUC_ONE_ADD]
           (SPECL [m,n] arithmeticTheory.NOT_GREATER_EQ));

val NOT_GREAT_NORM_CONV = REWR_CONV arithmeticTheory.NOT_GREATER;

val NOT_LEQ_NORM_CONV =
   if dense
   then REWR_CONV (TRANS (SPECL [m,n] arithmeticTheory.NOT_LEQ)
                         (SYM (SPECL [n,m] arithmeticTheory.LESS_EQ)))
   else REWR_CONV
         (SUBS [SPEC n arithmeticTheory.SUC_ONE_ADD] 
               (SPECL [m,n] arithmeticTheory.NOT_LEQ));

val NOT_LESS_NORM_CONV = REWR_CONV arithmeticTheory.NOT_LESS;

val NOT_NUM_EQ_NORM_CONV =
   if dense
   then REWR_CONV
         (SUBS [SYM (SPECL [m,n] arithmeticTheory.LESS_EQ),
                SYM (SPECL [n,m] arithmeticTheory.LESS_EQ)]
           (SPECL [m,n] arithmeticTheory.NOT_NUM_EQ))
   else REWR_CONV
         (SUBS [SPEC m arithmeticTheory.SUC_ONE_ADD,
                SPEC n arithmeticTheory.SUC_ONE_ADD]
           (SPECL [m,n] arithmeticTheory.NOT_NUM_EQ));

val ONE_MULT_CONV = REWR_CONV ONE_MULT;

val PLUS_ZERO_CONV = REWR_CONV PLUS_ZERO;

val SYM_ADD_ASSOC_CONV = REWR_CONV (GSYM arithmeticTheory.ADD_ASSOC);

val ZERO_MULT_CONV = REWR_CONV ZERO_MULT;

val ZERO_MULT_PLUS_CONV =
 REWR_CONV
  (SUBS
    [SYM (CONJUNCT1 (SPECL [--`a:num`--,--`b:num`--]
         arithmeticTheory.MULT_CLAUSES))]
    (SPEC (--`b:num`--) (GEN_ALL (CONJUNCT1 arithmeticTheory.ADD_CLAUSES))));

val ZERO_PLUS_CONV = REWR_CONV ZERO_PLUS;

(*===========================================================================*)
(* Conversions for rewriting inequalities                                    *)
(*===========================================================================*)

val EQ_PLUS_CONV =
 REWR_CONV
  (SUBS [SPECL [m,p] (arithmeticTheory.ADD_SYM),
         SPECL [n,p] (arithmeticTheory.ADD_SYM)]
    (SPECL [m,n,p] (arithmeticTheory.EQ_MONO_ADD_EQ)));

val LEQ_PLUS_CONV = REWR_CONV (arithmeticTheory.ADD_MONO_LESS_EQ);

val LESS_PLUS_CONV =
 REWR_CONV
  (SUBS [SPECL [m,p] (arithmeticTheory.ADD_SYM),
         SPECL [n,p] (arithmeticTheory.ADD_SYM)]
    (SPECL [m,n,p] (arithmeticTheory.LESS_MONO_ADD_EQ)));

(*===========================================================================*)
(* Conversions for normalising and eliminating subtraction                   *)
(*===========================================================================*)

val NUM_COND_RATOR_CONV =
 REWR_CONV
  (INST_TYPE [alpha |-> num] COND_RATOR);

val NUM_COND_RAND_CONV =
 REWR_CONV
   (INST_TYPE [alpha |-> num] COND_RAND);

val SUB_NORM_CONV =
 GEN_REWRITE_CONV I Rewrite.empty_rewrites 
 [arithmeticTheory.SUB_LEFT_ADD,         arithmeticTheory.SUB_RIGHT_ADD,
  arithmeticTheory.SUB_LEFT_SUB,         arithmeticTheory.SUB_RIGHT_SUB,
  arithmeticTheory.LEFT_SUB_DISTRIB,     arithmeticTheory.RIGHT_SUB_DISTRIB,
  arithmeticTheory.SUB_LEFT_SUC,
  arithmeticTheory.SUB_LEFT_LESS_EQ,     arithmeticTheory.SUB_RIGHT_LESS_EQ,
  arithmeticTheory.SUB_LEFT_LESS,        arithmeticTheory.SUB_RIGHT_LESS,
  arithmeticTheory.SUB_LEFT_GREATER_EQ,  arithmeticTheory.SUB_RIGHT_GREATER_EQ,
  arithmeticTheory.SUB_LEFT_GREATER,     arithmeticTheory.SUB_RIGHT_GREATER,
  arithmeticTheory.SUB_LEFT_EQ,          arithmeticTheory.SUB_RIGHT_EQ,
  arithmeticTheory.PRE_SUB1
 ];

(*
(*---------------------------------------------------------------------------
     jrh says that the following does a better job ...
 ---------------------------------------------------------------------------*)

local open arithmeticTheory
      val SUB_ELIM_CONV = Ho_resolve.HIGHER_REWRITE_CONV[SUB_ELIM_THM]
      val PRE_ELIM_CONV = Ho_resolve.HIGHER_REWRITE_CONV[PRE_ELIM_THM]
in
  val SUB_NORM_CONV = SUB_ELIM_CONV ORELSEC PRE_ELIM_CONV
end;
*)

end;
