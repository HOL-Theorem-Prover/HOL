(* ===================================================================== *)
(* FILE          : thm.sig                                               *)
(* DESCRIPTION   : Signature for the abstract data type of theorems.     *)
(*                 Most of the inference rules have been translated from *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 10, 1991                                    *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(*               : June 16, 1998, Konrad Slind                           *)
(* ===================================================================== *)


signature Thm =
sig
  type tag = Tag.tag
  type thm

  val tag      : thm -> tag
  val hyp      : thm -> Term.term list
  val concl    : thm -> Term.term
  val dest_thm : thm ->  Term.term list * Term.term
  val hyp_union     : thm list -> Term.term list
  val thm_free_vars : thm -> Term.term list

  (* The primitive rules of inference *)
  val ASSUME    : Term.term -> thm
  val REFL      : Term.term -> thm
  val BETA_CONV : Term.term -> thm
  val ABS       : Term.term -> thm -> thm
  val DISCH     : Term.term -> thm -> thm
  val MP        : thm -> thm -> thm
  val SUBST     : (Term.term,thm)Lib.subst -> Term.term -> thm -> thm
  val INST_TYPE : (Type.hol_type,Type.hol_type)Lib.subst -> thm -> thm


  (* The primitive-but-derivable rules of inference *)

  (* Lambda calculus *)
  val ALPHA : Term.term -> Term.term -> thm
  val MK_COMB : thm * thm -> thm
  val AP_TERM : Term.term -> thm -> thm
  val AP_THM : thm -> Term.term -> thm
  val ETA_CONV : Term.term -> thm

  (* Equality *)
  val SYM : thm -> thm
  val TRANS : thm -> thm -> thm
  val EQ_MP : thm -> thm -> thm
  val EQ_IMP_RULE : thm -> thm * thm
  val INST : (Term.term,Term.term)Lib.subst -> thm -> thm

  (* Forall *)
  val SPEC : Term.term -> thm -> thm
  val GEN : Term.term -> thm -> thm

  (* Exists *)
  val EXISTS : Term.term * Term.term -> thm -> thm
  val CHOOSE : Term.term * thm -> thm -> thm

  (* Conjunction *)
  val CONJ : thm -> thm -> thm
  val CONJUNCT1 : thm -> thm
  val CONJUNCT2 : thm -> thm

  (* Disjunction *)
  val DISJ1 : thm -> Term.term -> thm
  val DISJ2 : Term.term -> thm -> thm
  val DISJ_CASES : thm -> thm -> thm -> thm

  (* Negation *)
  val NOT_INTRO : thm -> thm
  val NOT_ELIM  : thm -> thm
  val CCONTR : Term.term -> thm -> thm


  (* Oracles and "system" theorems *)
  val mk_oracle_thm : tag -> Term.term list * Term.term -> thm
  val mk_tac_thm    : Term.term list * Term.term -> thm
  val mk_thm        : Term.term list * Term.term -> thm
  val disk_thm
     : Term.term vector -> string * 'a frag list list * 'a frag list -> thm


  (* Information hiding *)
  val Theory_init : (string ref * Term.term -> thm) ref      (* mk_axiom_thm *)
                        -> (tag -> Term.term -> thm) ref      (* mk_defn_thm *)
                           -> unit
  val Const_def_init : tag ref -> unit
end;
