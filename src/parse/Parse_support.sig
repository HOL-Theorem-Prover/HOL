signature Parse_support =
sig
  type env
  type preterm_in_env = env -> Preterm.preterm * env
  type bvar_in_env    = env -> (Preterm.preterm -> Preterm.preterm) * env
  type binder_in_env  = string -> bvar_in_env

val make_preterm : preterm_in_env -> Preterm.preterm
val make_aq : Term.term -> preterm_in_env
val make_binding_occ :(int,Type.hol_type) Lib.istream
                       -> string -> binder_in_env
val make_aq_binding_occ :(int,Type.hol_type) Lib.istream
                           -> Term.term -> binder_in_env
val make_atom: (int,Type.hol_type)Lib.istream -> string -> preterm_in_env
val make_string: string -> preterm_in_env
val list_make_comb : preterm_in_env list -> preterm_in_env
val bind_term :string -> binder_in_env list -> preterm_in_env -> preterm_in_env
val bind_restr_term : (int,Type.hol_type) Lib.istream
                      -> string
                      -> binder_in_env list
                      -> preterm_in_env
                      -> preterm_in_env
                      -> preterm_in_env
val make_vstruct : (int,Type.hol_type) Lib.istream
                    -> binder_in_env list
                    -> Type.hol_type option
                    -> binder_in_env
val make_constrained : preterm_in_env -> Type.hol_type -> preterm_in_env
val make_let : (int,Type.hol_type) Lib.istream
                -> (binder_in_env list * preterm_in_env) list
                  -> preterm_in_env -> preterm_in_env
val make_set : (int,Type.hol_type) Lib.istream
                -> preterm_in_env list -> preterm_in_env
val make_set_abs : (int,Type.hol_type) Lib.istream
                    -> preterm_in_env * preterm_in_env -> preterm_in_env

val hidden : string -> bool
val hide : string -> unit
val reveal : string -> unit

val binder_restrictions :unit -> (string * string) list
val associate_restriction :(string*string) -> unit
val delete_restriction :string -> unit

end;
