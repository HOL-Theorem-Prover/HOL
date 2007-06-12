signature Normal = 
sig
  include Abbrev

  val PRE_PROCESS_RULE : thm -> thm
  val SUBST_2_RULE : thm * thm -> thm -> thm
  val Normalize_Atom_Cond : thm * thm * thm * thm -> conv
  val K_Normalize : conv
  val normalize : thm -> thm
  val identify_atom : term -> term
  val beta_reduction : thm -> thm
  val ELIM_LET_RULE : thm -> thm
  val FLATTEN_LET_RULE : thm -> thm
  val to_ssa : string -> term -> term
  val SSA_CONV : conv
  val SSA_RULE : thm -> thm
end
