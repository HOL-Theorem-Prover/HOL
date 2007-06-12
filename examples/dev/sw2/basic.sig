signature basic =
sig
  include Abbrev
  val is_word_literal : term -> bool
  val is_atom : term -> bool 
  val is_binop : term -> bool 
  val is_cmpop : term -> bool 
  val is_relop : term -> bool 
  val is_atom_cond : term -> bool 
  val subst_exp : (term,term) subst -> term -> term
  val occurs_in : term -> term -> bool 
  val abs_fun : thm -> thm
end
