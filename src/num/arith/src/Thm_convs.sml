(*****************************************************************************)
(* FILE          : thm_convs.sml                                             *)
(* DESCRIPTION   : Conversions for rewriting with arithmetic theorems.       *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 5th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th November 1995                                        *)
(*****************************************************************************)

structure Thm_convs :> Thm_convs =
struct

open Arbint HolKernel Parse boolTheory Drule Theorems;

val GSYM      = Conv.GSYM;
val REWR_CONV = Conv.REWR_CONV;
val GEN_REWRITE_CONV = Rewrite.GEN_REWRITE_CONV;

local  (* Fix the grammar used by this file *)
  val ambient_grammars = Parse.current_grammars();
  val _ = Parse.temp_set_grammars arithmeticTheory.arithmetic_grammars
in

(*===========================================================================*)
(* Conversions for rewriting Boolean terms                                   *)
(*===========================================================================*)

val CONJ_ASSOC_NORM_CONV = REWR_CONV (GSYM CONJ_ASSOC);

val DISJ_ASSOC_NORM_CONV = REWR_CONV (GSYM DISJ_ASSOC);

val EQ_EXPAND_CONV = REWR_CONV EQ_EXPAND;

val IMP_EXPAND_CONV = REWR_CONV IMP_DISJ_THM;

val IMP_F_EQ_F_CONV = REWR_CONV IMP_F_EQ_F;

val IMP_IMP_CONJ_IMP_CONV = REWR_CONV AND_IMP_INTRO;

val LEFT_DIST_NORM_CONV = REWR_CONV LEFT_AND_OVER_OR;

val NOT_CONJ_NORM_CONV =
 REWR_CONV
  (GEN_ALL (CONJUNCT1 (SPECL [--`t1:bool`--,--`t2:bool`--] DE_MORGAN_THM)));

val NOT_DISJ_NORM_CONV =
 REWR_CONV
  (GEN_ALL (CONJUNCT2 (SPECL [--`t1:bool`--,--`t2:bool`--] DE_MORGAN_THM)));

val NOT_NOT_NORM_CONV = REWR_CONV (CONJUNCT1 NOT_CLAUSES);

val OR_F_CONV = REWR_CONV (el 3 (CONJUNCTS (SPEC (--`x:bool`--) OR_CLAUSES)));

val RIGHT_DIST_NORM_CONV = REWR_CONV RIGHT_AND_OVER_OR;

(*===========================================================================*)
(* Conversions for rewriting arithmetic terms                                *)
(*===========================================================================*)

val ADD_ASSOC_CONV = REWR_CONV (arithmeticTheory.ADD_ASSOC);

val ADD_SYM_CONV = REWR_CONV (arithmeticTheory.ADD_SYM);

val GATHER_BOTH_CONV =
 REWR_CONV
  (SYM (SPECL [--`a:num`--,--`b:num`--,--`x:num`--]
         (arithmeticTheory.RIGHT_ADD_DISTRIB)));

val GATHER_LEFT_CONV =
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL [--`x:num`--,--`n:num`--]
                           (arithmeticTheory.MULT_CLAUSES)))]
    (SYM (SPECL [--`a:num`--,--`1`--,--`x:num`--]
           (arithmeticTheory.RIGHT_ADD_DISTRIB))));

val GATHER_NEITHER_CONV = REWR_CONV (GSYM (arithmeticTheory.TIMES2));

val GATHER_RIGHT_CONV =
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL [--`x:num`--,--`n:num`--]
                           (arithmeticTheory.MULT_CLAUSES)))]
    (SYM (SPECL [--`1`--,--`b:num`--,--`x:num`--]
           (arithmeticTheory.RIGHT_ADD_DISTRIB))));

val GEQ_NORM_CONV = REWR_CONV (arithmeticTheory.GREATER_EQ);

val GREAT_NORM_CONV =
 REWR_CONV
  (SUBS [SYM (SPECL [--`m:num`--,--`n:num`--]
                 (arithmeticTheory.GREATER_DEF)),
         SPEC (--`n:num`--) (arithmeticTheory.SUC_ONE_ADD)]
    (SPECL [--`n:num`--,--`m:num`--] (arithmeticTheory.LESS_EQ)));

val LEFT_ADD_DISTRIB_CONV =
 REWR_CONV (arithmeticTheory.LEFT_ADD_DISTRIB);

val LESS_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`m:num`--) (arithmeticTheory.SUC_ONE_ADD)]
    (SPECL [--`m:num`--,--`n:num`--] (arithmeticTheory.LESS_EQ)));

val MULT_ASSOC_CONV = REWR_CONV (arithmeticTheory.MULT_ASSOC);

val MULT_COMM_CONV = REWR_CONV MULT_COMM;

val NOT_GEQ_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`m:num`--) (arithmeticTheory.SUC_ONE_ADD)]
    (SPECL [--`m:num`--,--`n:num`--]
        (arithmeticTheory.NOT_GREATER_EQ)));

val NOT_GREAT_NORM_CONV = REWR_CONV (arithmeticTheory.NOT_GREATER);

val NOT_LEQ_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`n:num`--) (arithmeticTheory.SUC_ONE_ADD)]
    (SPECL [--`m:num`--,--`n:num`--] (arithmeticTheory.NOT_LEQ)));

val NOT_LESS_NORM_CONV = REWR_CONV (arithmeticTheory.NOT_LESS);

val NOT_NUM_EQ_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`m:num`--) (arithmeticTheory.SUC_ONE_ADD),
         SPEC (--`n:num`--) (arithmeticTheory.SUC_ONE_ADD)]
    (SPECL [--`m:num`--,--`n:num`--] (arithmeticTheory.NOT_NUM_EQ)));

val NUM_EQ_NORM_CONV = REWR_CONV (arithmeticTheory.EQ_LESS_EQ);

val PLUS_ZERO_CONV = REWR_CONV PLUS_ZERO;

val SYM_ADD_ASSOC_CONV = REWR_CONV (GSYM (arithmeticTheory.ADD_ASSOC));

val SYM_ONE_MULT_CONV = REWR_CONV (GEN_ALL (SYM (SPEC_ALL ONE_MULT)));

val ZERO_MULT_CONV = REWR_CONV ZERO_MULT;

val ZERO_MULT_PLUS_CONV =
 REWR_CONV
  (SUBS [SYM (CONJUNCT1 (SPECL [--`a:num`--,--`b:num`--]
                            (arithmeticTheory.MULT_CLAUSES)))]
   (SPEC (--`b:num`--)
       (GEN_ALL (CONJUNCT1 (arithmeticTheory.ADD_CLAUSES)))));

val ZERO_PLUS_CONV = REWR_CONV ZERO_PLUS;

(*===========================================================================*)
(* Conversions for rewriting inequalities                                    *)
(*===========================================================================*)

val LEQ_PLUS_CONV = REWR_CONV (arithmeticTheory.ADD_MONO_LESS_EQ);

(*===========================================================================*)
(* Conversions for final simplification                                      *)
(*===========================================================================*)

val FORALL_SIMP_CONV = REWR_CONV FORALL_SIMP;

(*===========================================================================*)
(* Conversions for normalising and eliminating subtraction                   *)
(*===========================================================================*)

val NUM_COND_RATOR_CONV =
     REWR_CONV (INST_TYPE [alpha |-> Type`:num`] COND_RATOR);

val NUM_COND_RAND_CONV =
     REWR_CONV (INST_TYPE [alpha |-> Type`:num`] COND_RAND);

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

(*===========================================================================*)
(* Conversions for normalising and eliminating conditionals                  *)
(*===========================================================================*)

val COND_RATOR_CONV  = REWR_CONV COND_RATOR
val COND_RAND_CONV   = REWR_CONV COND_RAND
val COND_EXPAND_CONV = REWR_CONV COND_EXPAND;

val _ = Parse.temp_set_grammars ambient_grammars
end;

end
