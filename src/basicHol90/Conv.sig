(* ===================================================================== *)
(* FILE          : conv.sig                                              *)
(* DESCRIPTION   : Signature for various conversions. Translated from    *)
(*                 hol88.                                                *)
(* AUTHORS       : (c) Many people at Cambridge:                         *)
(*                        Larry Paulson                                  *)
(*                        Mike Gordon                                    *)
(*                        Richard Boulton and                            *)
(*                        Tom Melham, University of Cambridge plus       *)
(*                     Paul Loewenstein, for hol88                       *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Conv =
sig
   type tactic = Abbrev.tactic;
   type conv = Abbrev.conv
   type thm = Thm.thm
   type term = Term.term
   type hol_type = Type.hol_type

   val INST_TY_TERM : (term,term)Lib.subst * (hol_type,hol_type)Lib.subst
                        -> thm -> thm
   val GSPEC      : thm -> thm
   val PART_MATCH : (term -> term) -> thm -> conv
   val REWR_CONV  : thm -> conv
   val MATCH_MP   : thm -> thm -> thm
   val LAND_CONV  : conv -> conv
   val RAND_CONV  : conv -> conv
   val RATOR_CONV : conv -> conv
   val ABS_CONV   : conv -> conv
   val FORK_CONV  : conv * conv -> conv
   val BINOP_CONV : conv -> conv
   val EVERY_DISJ_CONV : conv -> conv
   val EVERY_CONJ_CONV : conv -> conv
   val QUANT_CONV : conv -> conv
   val STRIP_QUANT_CONV : conv -> conv
   val BINDER_CONV : conv -> conv
   val LHS_CONV   : conv -> conv
   val RHS_CONV   : conv -> conv
   val NO_CONV    : conv
   val ALL_CONV   : conv
   val THENC      : conv * conv -> conv
   val ORELSEC    : conv * conv -> conv
   val FIRST_CONV : conv list -> conv
   val EVERY_CONV : conv list -> conv
   val REPEATC    : conv -> conv
   val CHANGED_CONV : conv -> conv
   val TRY_CONV   : conv -> conv
   val SUB_CONV   : conv -> conv
   val DEPTH_CONV : conv -> conv
   val REDEPTH_CONV    : conv -> conv
   val TOP_DEPTH_CONV  : conv -> conv
   val TOP_SWEEP_CONV  : conv -> conv
   val ONCE_DEPTH_CONV : conv -> conv
   val CONV_RULE : conv -> thm -> thm
   val CONV_TAC  : conv -> tactic
   val BETA_RULE : thm -> thm
   val BETA_TAC  : tactic
   val NOT_FORALL_CONV : conv
   val NOT_EXISTS_CONV : conv
   val EXISTS_NOT_CONV : conv
   val FORALL_NOT_CONV : conv
   val FORALL_AND_CONV : conv
   val EXISTS_OR_CONV  : conv
   val AND_FORALL_CONV : conv
   val LEFT_AND_FORALL_CONV : conv
   val RIGHT_AND_FORALL_CONV : conv
   val OR_EXISTS_CONV : conv
   val LEFT_OR_EXISTS_CONV : conv
   val RIGHT_OR_EXISTS_CONV : conv
   val EXISTS_AND_CONV : conv
   val AND_EXISTS_CONV : conv
   val LEFT_AND_EXISTS_CONV : conv
   val RIGHT_AND_EXISTS_CONV : conv
   val FORALL_OR_CONV : conv
   val OR_FORALL_CONV : conv
   val LEFT_OR_FORALL_CONV : conv
   val RIGHT_OR_FORALL_CONV : conv
   val FORALL_IMP_CONV : conv
   val LEFT_IMP_EXISTS_CONV : conv
   val RIGHT_IMP_FORALL_CONV : conv
   val EXISTS_IMP_CONV : conv
   val LEFT_IMP_FORALL_CONV : conv
   val RIGHT_IMP_EXISTS_CONV : conv
   val X_SKOLEM_CONV : term -> conv
   val SKOLEM_CONV : conv
   val SYM_CONV : conv
   val RIGHT_CONV_RULE : conv -> thm -> thm
   val FUN_EQ_CONV : conv
   val X_FUN_EQ_CONV : term -> conv
   val SELECT_CONV : conv
   val CONTRAPOS_CONV : conv
   val ANTE_CONJ_CONV : conv
   val SWAP_EXISTS_CONV : conv
   val bool_EQ_CONV : conv
   val EXISTS_UNIQUE_CONV : conv
   val COND_CONV : conv
   val EXISTENCE : thm -> thm
   val AC_CONV : thm * thm -> conv
   val GSYM : thm -> thm

   (* Conversions for messing with bound variables *)
   (* renames variables under \ ! ? ?! or @ *)
   val RENAME_VARS_CONV : string list -> conv

   (* swaps variables under ! and ?, e.g, given !x y. ...
      gives   !y x. ... *)
   val SWAP_VARS_CONV : conv
end;
