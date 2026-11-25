signature shortWeierstrassSyntax =
sig
  type term = Term.term
  type hol_type = Type.hol_type

  val mk_sw_point_type : hol_type -> hol_type
  val ECInfinity_tm : term
  val ECAffine_tm : term
  val sw_add_tm : term
  val sw_group_tm : term
  val mk_ECInfinity : hol_type -> term
  val mk_ECAffine : term * term -> term
  val mk_ShortWeierstrassCurve : term * term * term -> term
  val mk_sw_points : term * term * term -> term
  val mk_sw_group : term * term * term -> term
  val mk_sw_add : term * term * term * term * term -> term

  (* Scalar syntax is monoid_exp (sw_group r a b) P n. *)
  val mk_sw_scalar : term * term * term * term * term -> term
  val dest_sw_scalar : term -> term * term * term * term * term
end
