signature parse_rank =
sig

type ('a,'b) rankconstructors =
     {intrank : int -> 'a,
      antiq : 'b -> 'a}

  val parse_rank :
    ('a,'b) rankconstructors ->
    'b qbuf.qbuf -> 'a

  val rk_antiq      : Kind.rank -> Kind.kind
  val dest_rk_antiq : Kind.kind -> Kind.rank
  val is_rk_antiq   : Kind.kind -> bool

  val rk_kd_antiq      : Kind.rank -> Type.hol_type
  val dest_rk_kd_antiq : Type.hol_type -> Kind.rank
  val is_rk_kd_antiq   : Type.hol_type -> bool

  val rk_ty_antiq      : Kind.rank -> Term.term
  val dest_rk_ty_antiq : Term.term -> Kind.rank
  val is_rk_ty_antiq   : Term.term -> bool

    (* The record of functions specify how to deal with the need to
       construct numeric ranks and antiquotations *)

end
