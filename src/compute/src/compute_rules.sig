signature compute_rules = sig

include Abbrev

datatype ('a,'b,'c,'d,'e) stack =
    Ztop
  | Zrator   of { Rand  : 'a, Ctx : ('a,'b,'c,'d,'e) stack }
  | Zrand    of { Rator : 'b, Ctx : ('a,'b,'c,'d,'e) stack }
  | Zabs     of { Bvar  : 'c, Ctx : ('a,'b,'c,'d,'e) stack }
  | Ztyrator of { Rand  : 'd, Ctx : ('a,'b,'c,'d,'e) stack }
  | Ztyabs   of { Bvar  : 'e, Ctx : ('a,'b,'c,'d,'e) stack }

exception DEAD_CODE of string

(* An abstraction of the Thm.thm type, only for testing purposes *)
(* type thm (*= Thm.thm*) *)

val rhs_concl : thm -> Term.term
val evaluate  : thm -> Thm.thm

val push_in_stk :  ('a -> 'b) ->
      'a * (thm * ((thm->thm->thm) * (thm * 'b), 'c, 'd, 'e, 'f) stack) ->
            thm * ((thm->thm->thm) * (thm * 'b), 'c, 'd, 'e, 'f) stack
val push_lam_in_stk :
      thm * ('a, 'b, thm->thm, 'c, 'd) stack ->
      thm * ('a, 'b, thm->thm, 'c, 'd) stack

val refl_thm  : Term.term -> thm
val trans_thm : thm -> Thm.thm -> thm
val beta_thm  : thm -> thm


val lazyfy_thm    : Thm.thm -> Thm.thm
val strictify_thm : Thm.thm -> Thm.thm
val eq_intro      : Thm.thm -> Thm.thm


end;
