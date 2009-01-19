signature Parse_support =
sig
  type pretype = Pretype.pretype
  type preterm = Preterm.preterm
  type term    = Term.term

  type env
  type preterm_in_env = env -> preterm * env
  type bvar_in_env    = env -> (preterm -> preterm) * env
  type overload_info  = term_grammar.overload_info

  val gen_overloaded_const  : overload_info -> locn.locn -> string -> preterm
  val make_preterm          : preterm_in_env -> preterm
  val make_aq               : locn.locn -> term -> preterm_in_env
  val make_binding_occ      : locn.locn -> string -> bvar_in_env
  val make_aq_binding_occ   : locn.locn -> term -> bvar_in_env
  val make_atom             : overload_info -> locn.locn ->
                              string -> preterm_in_env
  val make_qconst           : overload_info -> locn.locn -> string * string ->
                              preterm_in_env
  val list_make_comb        : locn.locn -> preterm_in_env list -> preterm_in_env
  val bind_term             : locn.locn -> bvar_in_env list ->
                              preterm_in_env -> preterm_in_env
  val make_vstruct          : overload_info -> locn.locn -> bvar_in_env list ->
                              pretype option -> bvar_in_env
  val make_constrained      : locn.locn -> preterm_in_env -> pretype ->
                              preterm_in_env
  val make_let              : overload_info -> locn.locn ->
                              (bvar_in_env list * preterm_in_env) list ->
                              preterm_in_env -> preterm_in_env
  val make_set_abs          : overload_info -> locn.locn ->
                              preterm_in_env * preterm_in_env ->
                              preterm_in_env

  val make_case_arrow       : overload_info -> locn.locn ->
                              preterm_in_env -> preterm_in_env ->
                              preterm_in_env

  val binder_restrictions   : unit -> (string * string) list
  val associate_restriction : locn.locn -> string * string -> unit
  val delete_restriction    : locn.locn -> string -> unit

end
