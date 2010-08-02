signature Drule =
sig
  include Abbrev

  val ETA_CONV         : term -> thm
  val RIGHT_ETA        : thm -> thm
  val EXT              : thm -> thm
  val MK_ABS           : thm -> thm
  val MK_EXISTS        : thm -> thm
  val LIST_MK_EXISTS   : term list -> thm -> thm
  val SIMPLE_EXISTS    : term -> thm -> thm
  val SIMPLE_CHOOSE    : term -> thm -> thm
  val EQT_INTRO        : thm -> thm
  val GSUBS            : ((term,term)subst -> term -> term)
                           -> thm list -> thm -> thm
  val SUBST_CONV       : (term,thm)subst -> term -> term -> thm
  val ADD_ASSUM        : term -> thm -> thm
  val IMP_TRANS        : thm -> thm -> thm
  val IMP_ANTISYM_RULE : thm -> thm -> thm
  val CONTR            : term -> thm -> thm
  val UNDISCH          : thm -> thm
  val EQT_ELIM         : thm -> thm
  val SPECL            : term list -> thm -> thm
  val SELECT_INTRO     : thm -> thm
  val SELECT_ELIM      : thm -> term * thm -> thm
  val SELECT_RULE      : thm -> thm
  val SPEC_VAR         : thm -> term * thm
  val FORALL_EQ        : term -> thm -> thm
  val EXISTS_EQ        : term -> thm -> thm
  val SELECT_EQ        : term -> thm -> thm
  val SUBS             : thm list -> thm -> thm
  val SUBS_OCCS        : (int list * thm) list -> thm -> thm
  val RIGHT_BETA       : thm -> thm
  val LIST_BETA_CONV   : term -> thm
  val RIGHT_LIST_BETA  : thm -> thm
  val CONJUNCTS_AC     : term * term -> thm
  val DISJUNCTS_AC     : term * term -> thm
  val CONJ_DISCH       : term -> thm -> thm
  val CONJ_DISCHL      : term list -> thm -> thm
  val NEG_DISCH        : term -> thm -> thm
  val NOT_EQ_SYM       : thm -> thm
  val EQF_INTRO        : thm -> thm
  val EQF_ELIM         : thm -> thm
  val ISPEC            : term -> thm -> thm
  val ISPECL           : term list -> thm -> thm
  val GEN_ALL          : thm -> thm
  val DISCH_ALL        : thm -> thm
  val UNDISCH_ALL      : thm -> thm
  val SPEC_ALL         : thm -> thm
  val PROVE_HYP        : thm -> thm -> thm
  val CONJ_PAIR        : thm -> thm * thm
  val LIST_CONJ        : thm list -> thm
  val CONJ_LIST        : int -> thm -> thm list
  val CONJUNCTS        : thm -> thm list
  val BODY_CONJUNCTS   : thm -> thm list
  val IMP_CANON        : thm -> thm list
  val MP_GENEQ_CANON   : bool list -> thm -> thm
  val MP_CANON         : thm -> thm
  val MP_LEQ_CANON     : thm -> thm
  val MP_REQ_CANON     : thm -> thm
  val LIST_MP          : thm list -> thm -> thm
  val CONTRAPOS        : thm -> thm
  val DISJ_IMP         : thm -> thm
  val IMP_ELIM         : thm -> thm
  val DISJ_CASES_UNION : thm -> thm -> thm -> thm
  val DISJ_CASESL      : thm -> thm list -> thm
  val ALPHA_CONV       : term -> term -> thm
  val GEN_ALPHA_CONV   : term -> term -> thm
  val IMP_CONJ         : thm -> thm -> thm
  val EXISTS_IMP       : term -> thm -> thm
  val INST_TY_TERM     : (term,term)subst * (hol_type,hol_type)subst
                          -> thm -> thm
  val GSPEC            : thm -> thm

  val PART_MATCH       : (term -> term) -> thm -> term -> thm
  val MATCH_MP         : thm -> thm -> thm
  val BETA_VAR         : term -> term -> term -> thm
  val HO_PART_MATCH    : (term -> term) -> thm -> term -> thm
  val HO_MATCH_MP      : thm -> thm -> thm
  val RES_CANON        : thm -> thm list

  val prove_rep_fn_one_one : thm -> thm
  val prove_rep_fn_onto    : thm -> thm
  val prove_abs_fn_onto    : thm -> thm
  val prove_abs_fn_one_one : thm -> thm

  val define_new_type_bijections
    : {name:string, ABS:string, REP:string, tyax:thm} -> thm

  val MK_AC_LCOMM    : thm * thm -> thm * thm * thm
end
