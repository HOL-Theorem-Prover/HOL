signature Thm =
sig

  include FinalThm where type hol_type = Type.hol_type
                     and type term = Term.term
                     and type tag = Tag.tag

  datatype proof =
    Axiom_prf
  | ABS_prf of term * thm
  | ALPHA_prf of term * term
  | AP_TERM_prf of term * thm
  | AP_THM_prf of thm * term
  | ASSUME_prf of term
  | BETA_CONV_prf of term
  | DISCH_prf of term * thm
  | EQ_IMP_RULE1_prf of thm
  | EQ_IMP_RULE2_prf of thm
  | EQ_MP_prf of thm * thm
  | GEN_ABS_prf of term option * term list * thm
  | INST_TYPE_prf of (hol_type,hol_type)Lib.subst * thm
  | INST_prf of (term,term)Lib.subst * thm
  | MK_COMB_prf of thm * thm
  | MP_prf of thm * thm
  | REFL_prf of term
  | SPEC_prf of term * thm
  | SUBST_prf of (term,thm)Lib.subst * term * thm
  | SYM_prf of thm
  | TRANS_prf of thm * thm
  | TODO_prf

  val proof : thm -> proof

end
