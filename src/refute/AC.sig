(*=======================================================================
 * Support for AC reasoning.
 *=====================================================================*)

signature AC =
sig
  include Abbrev

  val AC                : (thm * thm) -> term -> thm
  val CONJ_ACI          : term -> thm
  val AC_CANON_GEN_CONV : (thm * thm) -> (term * term -> order) -> conv
  val AC_CANON_CONV     : (thm * thm) -> conv
  val ASSOC_CONV        : thm -> conv
  val DISTRIB_CONV      : thm * thm -> conv
end

