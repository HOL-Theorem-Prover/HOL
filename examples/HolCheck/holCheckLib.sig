signature holCheckLib =
sig


type term_bdd = PrimitiveBddRules.term_bdd
type model = modelTools.model

val holCheck : model -> model

val mk_state :  Term.term -> (string * Term.term) list -> Term.term

val empty_model : model

val set_init : Term.term -> model -> model
val set_trans : (string * Term.term) list -> model -> model
val set_flag_ric : bool -> model -> model
val set_name : string -> model -> model
val set_vord : string list -> model -> model
val set_state : Term.term -> model -> model
val set_props :  (string * Term.term) list -> model -> model
val set_flag_abs : bool -> model -> model

val get_init : model -> Term.term
val get_trans : model -> (string * Term.term) list
val get_flag_ric : model -> bool
val get_name : model -> string option
val get_vord : model -> string list option
val get_state : model -> Term.term option
val get_props : model ->  (string * Term.term) list
val get_results : model -> (term_bdd * Thm.thm option * Term.term list option) list option
val get_flag_abs : model -> bool

val prove_model : model -> model

end
