signature parse_rank =
sig

type ('a,'b) rankconstructors =
     {intrank : int -> 'a,
      antiq : 'b -> 'a}

  val parse_rank :
    ('a,'b) rankconstructors ->
    'b qbuf.qbuf -> 'a

  val rk_antiq_kind      : Kind.rank -> Kind.kind
  val dest_rk_antiq_kind : Kind.kind -> Kind.rank
  val is_rk_antiq_kind   : Kind.kind -> bool

  val rk_antiq_type      : Kind.rank -> Type.hol_type
  val dest_rk_antiq_type : Type.hol_type -> Kind.rank
  val is_rk_antiq_type   : Type.hol_type -> bool

  val rk_antiq      : Kind.rank -> Term.term
  val dest_rk_antiq : Term.term -> Kind.rank
  val is_rk_antiq   : Term.term -> bool

    (* The record of functions specify how to deal with the need to
       construct numeric ranks and antiquotations *)

end
