(*========================================================================
 *  Higher Order Matching as a derived rule.
 *
 * Code ported from GTT to hol90 by DRS.
 *=======================================================================*)

signature Ho_match = 
sig
  type hol_type = Type.hol_type;
  type term = Term.term;
  type thm = Thm.thm;
  type conv = Abbrev.conv;

    val match_term : term list -> term -> 
                     term -> (term * term) list * (hol_type * hol_type) list
    val PART_MATCH : (term -> term) -> thm -> term -> thm
    val BETA_VAR : term -> term -> conv

end (* sig *)

