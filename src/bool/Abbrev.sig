signature Abbrev =
sig
  type thm          = Thm.thm
  type term         = Term.term
  type hol_type     = Type.hol_type
  type conv         = term -> thm
  type rule         = thm -> thm
  type goal         = term list * term
  type validation   = thm list -> thm
  type tactic       = goal -> goal list * validation
  type thm_tactic   = thm -> tactic
  type thm_tactical = thm_tactic -> thm_tactic
  type ppstream     = Portable.ppstream
  type 'a quotation = 'a Portable.frag list
  type ('a,'b)subst = ('a,'b) Lib.subst
  type defn         = DefnBase.defn
end
