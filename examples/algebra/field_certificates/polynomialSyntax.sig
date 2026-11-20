signature polynomialSyntax =
sig
  type term = Term.term
  type hol_type = Type.hol_type

  (* Grammar-independent constructors for the existing record-based algebra.
     Ring and polynomial constructors infer the coefficient type from their
     arguments. PolyRing and PolyModRing denote poly_ring and poly_mod_ring. *)
  val mk_ring_type : hol_type -> hol_type
  val GF_tm : term
  val mk_GF : term -> term
  val mk_Field : term -> term
  val mk_Poly : term * term -> term
  val mk_poly_monic : term * term -> term
  val mk_poly_deg : term * term -> term
  val poly_mod_tm : term
  val mk_poly_mod : term * term * term -> term
  val mk_poly_ring : term -> term
  val mk_poly_mod_ring : term * term -> term

  (* Record projections and the derived monoid exponent operation. *)
  val monoid_exp_tm : term
  val monoid_inv_tm : term
  val mk_ring_carrier : term -> term
  val mk_ring_sum : term -> term
  val mk_ring_prod : term -> term
  val mk_monoid_op : term -> term
  val mk_monoid_id : term -> term
  val mk_monoid_exp : term -> term
  val mk_monoid_inv : term -> term
end
