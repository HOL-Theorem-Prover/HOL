(* ===================================================================== *)
(* FILE          : drule.sig                                             *)
(* DESCRIPTION   : Signature for many derived rules of inference.        *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge, for hol88    *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)

signature Drule =
sig
  val EXT            : Thm.thm -> Thm.thm
  val MK_ABS         : Thm.thm -> Thm.thm
  val MK_EXISTS      : Thm.thm -> Thm.thm
  val EQT_INTRO      : Thm.thm -> Thm.thm
  val GSUBS       : ((Term.term,Term.term) Lib.subst -> Term.term -> Term.term)
                        -> Thm.thm list -> Thm.thm -> Thm.thm
  val SUBST_CONV     : (Term.term,Thm.thm)Lib.subst 
                        -> Term.term -> Term.term -> Thm.thm
  val ADD_ASSUM      : Term.term -> Thm.thm -> Thm.thm
  val IMP_TRANS      : Thm.thm -> Thm.thm -> Thm.thm
  val IMP_ANTISYM_RULE : Thm.thm -> Thm.thm -> Thm.thm
  val CONTR          : Term.term -> Thm.thm -> Thm.thm

  val UNDISCH        : Thm.thm -> Thm.thm
  val EQT_ELIM       : Thm.thm -> Thm.thm
  val SPECL          : Term.term list -> Thm.thm -> Thm.thm
  val GENL           : Term.term list -> Thm.thm -> Thm.thm
  val SELECT_INTRO   : Thm.thm -> Thm.thm
  val SELECT_ELIM    : Thm.thm -> Term.term * Thm.thm -> Thm.thm
  val SELECT_RULE    : Thm.thm -> Thm.thm
  val SPEC_VAR       : Thm.thm -> Term.term * Thm.thm
  val LIST_MK_EXISTS : Term.term list -> Thm.thm -> Thm.thm
  val FORALL_EQ      : Term.term -> Thm.thm -> Thm.thm
  val EXISTS_EQ      : Term.term -> Thm.thm -> Thm.thm
  val SELECT_EQ      : Term.term -> Thm.thm -> Thm.thm
  val SUBS           : Thm.thm list -> Thm.thm -> Thm.thm
  val SUBS_OCCS      : (int list * Thm.thm) list -> Thm.thm -> Thm.thm
  val RIGHT_BETA     : Thm.thm -> Thm.thm
  val LIST_BETA_CONV : Term.term -> Thm.thm
  val RIGHT_LIST_BETA: Thm.thm -> Thm.thm
  val CONJUNCTS_CONV : Term.term * Term.term -> Thm.thm
  val CONJ_SET_CONV  : Term.term list -> Term.term list -> Thm.thm
  val FRONT_CONJ_CONV: Term.term list -> Term.term -> Thm.thm
  val CONJ_DISCH     : Term.term -> Thm.thm -> Thm.thm
  val CONJ_DISCHL    : Term.term list -> Thm.thm -> Thm.thm
  val NEG_DISCH      : Term.term -> Thm.thm -> Thm.thm
  val NOT_EQ_SYM     : Thm.thm -> Thm.thm
  val EQF_INTRO      : Thm.thm -> Thm.thm
  val EQF_ELIM       : Thm.thm -> Thm.thm
  val ISPEC          : Term.term -> Thm.thm -> Thm.thm
  val ISPECL         : Term.term list -> Thm.thm -> Thm.thm
  val GEN_ALL        : Thm.thm -> Thm.thm
  val DISCH_ALL      : Thm.thm -> Thm.thm
  val UNDISCH_ALL    : Thm.thm -> Thm.thm
  val SPEC_ALL       : Thm.thm -> Thm.thm
  val PROVE_HYP      : Thm.thm -> Thm.thm -> Thm.thm
  val CONJ_PAIR      : Thm.thm -> Thm.thm * Thm.thm
  val LIST_CONJ      : Thm.thm list -> Thm.thm
  val CONJ_LIST      : int -> Thm.thm -> Thm.thm list
  val CONJUNCTS      : Thm.thm -> Thm.thm list
  val BODY_CONJUNCTS : Thm.thm -> Thm.thm list
  val IMP_CANON      : Thm.thm -> Thm.thm list
  val LIST_MP        : Thm.thm list -> Thm.thm -> Thm.thm
  val CONTRAPOS      : Thm.thm -> Thm.thm
  val DISJ_IMP       : Thm.thm -> Thm.thm
  val IMP_ELIM       : Thm.thm -> Thm.thm
  val DISJ_CASES_UNION : Thm.thm -> Thm.thm -> Thm.thm -> Thm.thm
  val DISJ_CASESL    : Thm.thm -> Thm.thm list -> Thm.thm
  val ALPHA_CONV     : Term.term -> Term.term -> Thm.thm
  val GEN_ALPHA_CONV : Term.term -> Term.term -> Thm.thm
  val IMP_CONJ       : Thm.thm -> Thm.thm -> Thm.thm
  val EXISTS_IMP     : Term.term -> Thm.thm -> Thm.thm
end;
