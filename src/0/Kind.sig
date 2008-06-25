signature Kind =
sig
  type kind = KernelTypes.kind

  val typ           : kind
  val ==>           : (kind * kind) -> kind  (* infixr 3 ==> *)
  val kind_dom_rng  : kind -> (kind * kind)  (* inverts ==>  *)
  val mk_arity      : int -> kind
  val is_arity      : kind -> bool
  val arity_of      : kind -> int
  val kind_compare  : kind * kind -> order
  val pp_kind       : ppstream -> kind -> unit
  val pp_qkind      : ppstream -> kind -> unit
  val kind_to_string: kind -> string
end
