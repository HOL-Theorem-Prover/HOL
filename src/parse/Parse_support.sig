signature Parse_support =
sig
  type pretype = Pretype.pretype
  type preterm = Preterm.preterm
  type term    = Term.term

  type env
  type preterm_in_env = env -> preterm * env
  type bvar_in_env    = env -> (preterm -> preterm) * env
  type binder_in_env  = string -> bvar_in_env

  val gen_overloaded_const: term_grammar.overload_info -> string -> preterm
  val make_preterm        : preterm_in_env -> preterm
  val make_aq             : term -> preterm_in_env
  val make_binding_occ    : string -> binder_in_env
  val make_aq_binding_occ : term -> binder_in_env
  val make_atom           : term_grammar.overload_info
                             -> string -> preterm_in_env
  val make_qconst         : term_grammar.overload_info
                             -> string * string -> preterm_in_env
  val list_make_comb      : preterm_in_env list -> preterm_in_env
  val bind_term           : string -> binder_in_env list
                              -> preterm_in_env -> preterm_in_env
  val bind_restr_term     : string -> binder_in_env list
                             -> preterm_in_env -> preterm_in_env
                              -> preterm_in_env
  val make_vstruct        : binder_in_env list
                             -> pretype option -> binder_in_env
  val make_constrained    : preterm_in_env -> pretype -> preterm_in_env
  val make_let            : (binder_in_env list * preterm_in_env) list
                              -> preterm_in_env -> preterm_in_env
  val make_set_abs        : preterm_in_env * preterm_in_env -> preterm_in_env

  val binder_restrictions   :unit -> (string * string) list
  val associate_restriction :string * string -> unit
  val delete_restriction    :string -> unit

end
