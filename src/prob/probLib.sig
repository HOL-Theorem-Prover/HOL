signature probLib =
sig
   type term = Term.term
   type thm = Thm.thm

  val SHD_PSEUDO_CONV : term -> thm
  val STL_PSEUDO_CONV : term -> thm
  val UNIFORM_CONV    : term -> thm

end
