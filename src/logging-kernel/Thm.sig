signature Thm =
sig

  include FinalThm where type hol_type = Type.hol_type
                     and type term = Term.term
                     and type tag = Tag.tag

  datatype proof =
    Axiom_prf
  | ASSUME_prf of term
  | REFL_prf of term
  | BETA_CONV_prf of term
  | ABS_prf of term * thm
  | DISCH_prf of term * thm
  | MP_prf of thm * thm
  | SUBST_prf of (term,thm)Lib.subst * term * thm
  | INST_TYPE_prf of (hol_type,hol_type)Lib.subst * thm
  | TODO_prf

end
