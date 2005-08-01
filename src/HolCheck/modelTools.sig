signature modelTools =
sig
    include Abbrev

type term_bdd = PrimitiveBddRules.term_bdd
type model
type ic = internalCacheTools.ic

val empty_model : model

val get_init : model -> Term.term
val get_trans : model ->(string * Term.term) list 
val get_flag_ric : model -> bool
val get_name : model -> string option
val get_vord : model -> string list option
val get_state : model -> Term.term option
val get_props : model ->  (string * Term.term) list
val get_results : model -> (PrimitiveBddRules.term_bdd * Thm.thm option * Term.term list option) list option
val get_ic : model -> ic option
val get_flag_abs : model -> bool

val set_init : Term.term -> model -> model
val set_trans : (string * Term.term) list -> model -> model
val set_flag_ric : bool -> model -> model
val set_name : string -> model -> model
val set_vord : string list -> model -> model
val set_state : Term.term -> model -> model
val set_props :  (string * Term.term) list -> model -> model
val set_results : (PrimitiveBddRules.term_bdd * Thm.thm option * Term.term list option) list -> model -> model
val set_ic : ic -> model -> model
val set_flag_abs : bool -> model -> model


val dest_model : 
    model -> Term.term * (string * Term.term) list * bool * string option * string list option 
    * Term.term option * (string * Term.term) list 
    * (PrimitiveBddRules.term_bdd * Thm.thm option * Term.term list option) list option
    * ic option 

val prove_model : model -> model

end
