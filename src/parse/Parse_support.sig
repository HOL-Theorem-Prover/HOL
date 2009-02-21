signature Parse_support =
sig
  type prekind = Prekind.prekind
  type prerank = Prerank.prerank
  type pretype = Pretype.pretype
  type uvartype = Pretype.uvartype
  type preterm = Preterm.preterm
  type term    = Term.term

  type env
  type pretype_in_env = env -> pretype * env
  type preterm_in_env = env -> preterm * env
  type bvar_in_env    = env -> (preterm -> preterm) * env
  type btyvar_in_env  = env -> (pretype -> pretype) * env
(* ??? what happens to binder_in_env ??? becomes bvar_in_env ???
                 and tybinder_in_env ??? becomes btyvar_in_env ???
  type binder_in_env  = string -> bvar_in_env
  type tybinder_in_env = string -> btyvar_in_env
*)
  type overload_info  = term_grammar.overload_info

  val empty_env             : env
  val get_env               : env ->
           {scope      : (string * pretype) list,
            free       : (string * pretype) list,
            scope_ty   : (string * (prekind * prerank)) list,
            free_ty    : (string * (prekind * prerank)) list,
            uscore_cnt : int }
  val gen_overloaded_const  : overload_info -> locn.locn -> string -> preterm
  val make_pretype          : pretype_in_env -> pretype
  val make_preterm          : preterm_in_env -> preterm
  val make_aq               : locn.locn -> term -> preterm_in_env
  val make_binding_occ      : locn.locn -> string -> bvar_in_env
  val make_tybinding_occ    : locn.locn -> string -> prekind -> prerank -> bvar_in_env
  val make_aq_binding_occ   : locn.locn -> term -> bvar_in_env
  val make_binding_type_occ : locn.locn -> string -> string -> btyvar_in_env
  val make_kind_binding_occ : locn.locn -> btyvar_in_env -> prekind -> btyvar_in_env
  val make_rank_binding_occ : locn.locn -> btyvar_in_env -> prerank -> btyvar_in_env
  val make_kind_tybinding_occ : locn.locn -> bvar_in_env -> prekind -> bvar_in_env
  val make_rank_tybinding_occ : locn.locn -> bvar_in_env -> prerank -> bvar_in_env
  val make_atom             : overload_info -> locn.locn ->
                              string -> preterm_in_env
  val make_type_atom        : locn.locn -> (string * prekind * prerank) -> pretype_in_env
  val make_uvar_type        : locn.locn -> uvartype ref -> pretype_in_env option -> pretype_in_env
  val make_type_constant    : locn.locn -> {Thy:string,Tyop:string} -> pretype_in_env
  val make_qconst           : overload_info -> locn.locn -> string * string ->
                              preterm_in_env
  val list_make_comb        : locn.locn -> preterm_in_env list -> preterm_in_env
  val list_make_tycomb      : locn.locn -> preterm_in_env -> pretype_in_env list -> preterm_in_env
  val list_make_app_type    : locn.locn -> pretype_in_env list -> pretype_in_env
  val bind_term             : locn.locn -> bvar_in_env list ->
                              preterm_in_env -> preterm_in_env
  val bind_type             : locn.locn -> btyvar_in_env list ->
                              pretype_in_env -> pretype_in_env
  val make_vstruct          : overload_info -> locn.locn -> bvar_in_env list ->
                              pretype_in_env option -> bvar_in_env
  val make_constrained      : locn.locn -> preterm_in_env -> pretype_in_env -> preterm_in_env
  val make_kind_constr_type : locn.locn -> pretype_in_env -> prekind -> pretype_in_env
  val make_rank_constr_type : locn.locn -> pretype_in_env -> prerank -> pretype_in_env
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
