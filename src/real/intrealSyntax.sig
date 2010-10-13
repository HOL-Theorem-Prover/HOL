signature intrealSyntax =
sig

  include Abbrev

  (* terms and types *)

  val real_of_int_tm : term (* the injection from :int -> :real *)
  val INT_FLOOR_tm   : term
  val INT_CEILING_tm : term
  val is_int_tm      : term

  (* discriminators, constructors, etc. *)

  val mk_real_of_int   : term -> term
  val dest_real_of_int : term -> term
  val is_real_of_int   : term -> bool

  val mk_INT_FLOOR   : term -> term
  val dest_INT_FLOOR : term -> term
  val is_INT_FLOOR   : term -> bool

  val mk_INT_CEILING   : term -> term
  val dest_INT_CEILING : term -> term
  val is_INT_CEILING   : term -> bool

  val mk_is_int   : term -> term
  val dest_is_int : term -> term
  val is_is_int   : term -> bool

end
