structure Abbrev :> Abbrev =
struct
  type thm          = Thm.thm
  type term         = Term.term
  type hol_type     = Type.hol_type
  type conv         = term -> thm
  type rule         = thm -> thm
  type goal         = term list * term
  type validation   = thm list -> thm
  type tactic       = goal -> goal list * validation
  type list_validation   = thm list -> thm list
  type list_tactic  = goal list -> goal list * list_validation
  type ('a,'b) gentactic = 'a -> goal list * (thm list -> 'b)
  type thm_tactic   = thm -> tactic
  type thm_tactical = thm_tactic -> thm_tactic
  type 'a quotation = 'a Portable.frag list
  type ('a,'b)subst = ('a,'b) Lib.subst
end
