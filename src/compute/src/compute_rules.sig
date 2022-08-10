signature compute_rules = sig

include Abbrev

datatype ('a,'b,'c) stack =
    Ztop
  | Zrator of { Rand : 'a, Ctx : ('a,'b,'c) stack }
  | Zrand of { Rator : 'b, Ctx : ('a,'b,'c) stack }
  | Zabs of { Bvar : 'c, Ctx : ('a,'b,'c) stack }

exception DEAD_CODE of string

(* An abstraction of the Thm.thm type, only for testing purposes *)
(* type thm (*= Thm.thm*) *)

val rhs_concl : thm -> Term.term
val evaluate  : thm -> Thm.thm

val refl_thm  : Term.term -> thm
val trans_thm : thm -> Thm.thm -> thm
val beta_thm  : thm -> thm
val try_eta: thm -> thm

val lazyfy_thm    : Thm.thm -> Thm.thm
val strictify_thm : Thm.thm -> Thm.thm
val eq_intro      : Thm.thm -> Thm.thm

end
