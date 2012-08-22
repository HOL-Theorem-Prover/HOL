signature state_transformerSyntax =
sig

  include Abbrev

  val unit_tm : term
  val join_tm : term
  val bind_tm : term
  val mmap_tm : term
  val for_tm : term

  val mk_unit : term * hol_type -> term
  val mk_join : term -> term
  val mk_bind : term * term -> term
  val mk_mmap : term * term -> term
  val mk_for : term * term * term -> term

  val dest_unit : term -> term * hol_type
  val dest_join : term -> term
  val dest_bind : term -> term * term
  val dest_mmap : term -> term * term
  val dest_for : term -> term * term * term

  val is_unit : term -> bool
  val is_join : term -> bool
  val is_bind : term -> bool
  val is_mmap : term -> bool
  val is_for : term -> bool

end
