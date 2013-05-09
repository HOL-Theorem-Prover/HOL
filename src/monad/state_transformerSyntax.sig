signature state_transformerSyntax =
sig

  include Abbrev

  val mk_monad_type : hol_type * hol_type -> hol_type
  val dest_monad_type : hol_type -> hol_type * hol_type

  val bind_tm : term
  val for_tm : term
  val join_tm : term
  val mmap_tm : term
  val narrow_tm : term
  val read_tm : term
  val unit_tm : term
  val widen_tm : term
  val write_tm : term

  val mk_bind : term * term -> term
  val mk_for : term * term * term -> term
  val mk_join : term -> term
  val mk_mmap : term * term -> term
  val mk_narrow : term * term -> term
  val mk_read : term -> term
  val mk_unit : term * hol_type -> term
  val mk_widen : term * hol_type -> term
  val mk_write : term -> term

  val dest_bind : term -> term * term
  val dest_for : term -> term * term * term
  val dest_join : term -> term
  val dest_mmap : term -> term * term
  val dest_narrow : term -> term * term
  val dest_read : term -> term
  val dest_unit : term -> term * hol_type
  val dest_widen : term -> term * hol_type
  val dest_write : term -> term

  val is_bind : term -> bool
  val is_for : term -> bool
  val is_join : term -> bool
  val is_mmap : term -> bool
  val is_narrow : term -> bool
  val is_read : term -> bool
  val is_unit : term -> bool
  val is_widen : term -> bool
  val is_write : term -> bool

end
