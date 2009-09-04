signature Rules =
sig
 type ('a,'b) subst = ('a,'b)Lib.subst
 type term = Term.term
 type thm = Thm.thm


  val RIGHT_ASSOC      : thm -> thm
  val FILTER_DISCH_ALL : (term -> bool) -> thm -> thm

  val CHOOSE           : term * thm -> thm -> thm
  val EXISTS           : term * term -> thm -> thm
  val EXISTL           : term list -> thm -> thm
  val IT_EXISTS        : (term,term) subst -> thm -> thm

  val EVEN_ORS         : thm list -> thm list
  val DISJ_CASESL      : thm -> thm list -> thm

  val LEFT_ABS_VSTRUCT : thm -> thm
  val LEFT_EXISTS      : thm -> thm

  val SUBS             : thm list -> thm -> thm
  val simpl_conv       : thm list -> term -> thm
  val simplify         : thm list -> thm -> thm

end
