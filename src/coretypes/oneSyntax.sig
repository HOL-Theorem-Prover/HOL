signature oneSyntax =
sig
  include Abbrev

  val one_ty      : hol_type
  val one_tm      : term
  val one_case_tm : term
  val mk_one_case : term -> term
  val lift_one    : hol_type -> unit -> term
  val is_one      : term -> bool
end
