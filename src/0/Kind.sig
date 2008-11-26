signature Kind =
sig
  type kind = KernelTypes.kind

  val typ           : kind

  val mk_varkind    : string -> kind
  val gen_kdvar     : unit -> kind
  val dest_var_kind : kind -> string
  val is_var_kind   : kind -> bool
  val is_gen_kdvar  : kind -> bool
  val kappa         : kind

  val ==>           : (kind * kind) -> kind  (* infixr 3 ==> *)
  val is_opr_kind   : kind -> bool
  val kind_dom_rng  : kind -> (kind * kind)  (* inverts ==>  *)
  val mk_arity      : int -> kind
  val is_arity      : kind -> bool
  val arity_of      : kind -> int

  val kind_compare  : kind * kind -> order

  val kind_subst    : (kind,kind)Lib.subst -> kind -> kind
  val kind_vars     : kind -> kind list
  val kind_varsl    : kind list -> kind list
  val kind_var_in   : kind -> kind -> bool
  val exists_kdvar  : (kind -> bool) -> kind -> bool

  val match_kind    : kind -> kind -> (kind,kind)Lib.subst
  val raw_match_kind : kind -> kind
                       -> (kind,kind) Lib.subst * kind list
                       -> (kind,kind) Lib.subst * kind list
  val match_kind_restr : kind list -> kind -> kind ->
                         (kind,kind)Lib.subst
  val match_kind_in_context : kind -> kind
                              -> (kind,kind)Lib.subst
                              -> (kind,kind)Lib.subst

  val pp_kind       : ppstream -> kind -> unit
  val pp_qkind      : ppstream -> kind -> unit
  val kind_to_string: kind -> string
  val kind_size     : kind -> int
end
