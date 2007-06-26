signature basic =
sig
  include Abbrev
  val is_word_literal : term -> bool
  val is_atomic : term -> bool 
  val is_num_arithop : term -> bool 
  val is_word_arithop : term -> bool 
  val is_num_cmpop : term -> bool 
  val is_word_cmpop : term -> bool 
  val is_word_bitwiseop : term -> bool
  val is_word_shiftop : term -> bool
  val is_relop : term -> bool 
  val is_binop : term -> bool
  val is_atom_cond : term -> bool 
  val subst_exp : (term,term) subst -> term -> term
  val occurs_in : term -> term -> bool 
  val abs_fun : thm -> thm
end
