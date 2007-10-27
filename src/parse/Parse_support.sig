signature Parse_support =
sig
  type pretype = Pretype.pretype
  type preterm = Preterm.preterm
  type term    = Term.term

  type env
  type pretype_in_env = env -> pretype * env
  type preterm_in_env = env -> preterm * env
  type bvar_in_env    = env -> (preterm -> preterm) * env
  type binder_in_env  = string -> bvar_in_env

  val gen_overloaded_const  : term_grammar.overload_info -> locn.locn -> string -> preterm
  val make_preterm          : preterm_in_env -> preterm
  val make_aq               : locn.locn -> term -> preterm_in_env
  val make_binding_occ      : locn.locn -> string -> binder_in_env
  val make_tybinding_occ    : pretype -> binder_in_env
  val make_aq_binding_occ   : locn.locn -> term -> binder_in_env
  val make_atom             : term_grammar.overload_info
                               -> locn.locn -> string -> preterm_in_env
  val make_qconst           : term_grammar.overload_info
                               -> locn.locn -> string * string -> preterm_in_env
  val list_make_comb        : locn.locn -> preterm_in_env list -> preterm_in_env
  val list_make_tycomb      : locn.locn -> preterm_in_env -> pretype list -> preterm_in_env
  val bind_term             : locn.locn -> string -> binder_in_env list
                                -> preterm_in_env -> preterm_in_env
  val bind_restr_term       : locn.locn -> string -> binder_in_env list
                               -> preterm_in_env -> preterm_in_env
                                -> preterm_in_env
  val make_vstruct          : locn.locn -> binder_in_env list
                               -> pretype option -> binder_in_env
  val make_constrained      : locn.locn -> preterm_in_env -> pretype -> preterm_in_env
  val make_let              : locn.locn -> (binder_in_env list * preterm_in_env) list
                                -> preterm_in_env -> preterm_in_env
  val make_set_abs          : locn.locn -> preterm_in_env * preterm_in_env -> preterm_in_env
(*  val make_seq_abs          : locn.locn -> preterm_in_env * preterm_in_env -> preterm_in_env *)

  val binder_restrictions   : unit -> (string * string) list
  val associate_restriction : locn.locn -> string * string -> unit
  val delete_restriction    : locn.locn -> string -> unit

end
