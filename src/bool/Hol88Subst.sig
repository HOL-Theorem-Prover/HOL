signature Hol88Subst =
sig
  include Abbrev

  type ('a,'b)hol88subst = ('b * 'a) list

  val pair2recd     : 'b * 'a -> {redex:'a,residue:'b}
  val recd2pair     : {redex:'a,residue:'b} -> 'b * 'a
  val hol88subst_of : ('a,'b)subst -> ('a,'b)hol88subst
  val subst_of      : ('a,'b)hol88subst -> ('a,'b)subst

  val type_subst    : (hol_type,hol_type)hol88subst -> hol_type -> hol_type
  val match_type    : hol_type -> hol_type -> (hol_type,hol_type)hol88subst
  val subst         : (term,term)hol88subst -> term -> term
  val inst          : (hol_type,hol_type)hol88subst -> term -> term
  val subst_occs    : int list list -> (term,term)hol88subst -> term -> term
  val match_term    : term -> term 
                       -> (term,term)hol88subst * (hol_type,hol_type)hol88subst
  val SUBST         : (term,thm)hol88subst ->term -> thm -> thm
  val INST          : (term,term)hol88subst -> thm -> thm
  val INST_TYPE     : (hol_type,hol_type)hol88subst -> thm -> thm
  val SUBST_CONV    : (term,thm)hol88subst -> term -> term -> thm
  val INST_TY_TERM  : (term,term)hol88subst * (hol_type,hol_type)hol88subst
                        -> thm -> thm
end
