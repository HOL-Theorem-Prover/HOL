signature cv_miscLib =
sig

  include Abbrev

  val cv_rep_cv_tm : term -> term
  val cv_rep_cv_tm_conv : conv -> conv
  val cv_rep_from : term -> term
  val cv_rep_from_conv : conv -> conv
  val cv_rep_hol_tm : term -> term
  val cv_rep_hol_tm_conv : conv -> conv
  val cv_rep_pre : term -> term
  val cv_rep_pre_conv : conv -> conv
  val mk_cv_rep : term -> term -> term -> term -> term
  val is_cv_rep : term -> bool
  val is_cv_proj : term -> bool
  val dest_cv_proj : term -> term * term
  val cv_size_tm : term
  val mk_cv_size : term -> term

  val contains_fun_ty : hol_type -> bool

  val remove_fupd_conv : conv

end
