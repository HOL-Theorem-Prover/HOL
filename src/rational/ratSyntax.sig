signature ratSyntax =
sig
	type term = Term.term
	type hol_type = Abbrev.hol_type

	(*val rat	: hol_type*)

	val rat_0_tm	: term
	val rat_1_tm	: term

	val rat_nmr_tm	: term
	val rat_dnm_tm	: term
	val rat_sgn_tm	: term

	val rat_ainv_tm	: term
	val rat_minv_tm	: term

	val rat_add_tm	: term
	val rat_sub_tm	: term
	val rat_mul_tm	: term
	val rat_div_tm	: term

	val rat_les_tm	: term
	val rat_gre_tm	: term
	val rat_leq_tm	: term
	val rat_geq_tm	: term

	val mk_rat_nmr	: term -> term
	val mk_rat_dnm	: term -> term
	val mk_rat_sgn	: term -> term

	val mk_rat_ainv	: term -> term
	val mk_rat_minv	: term -> term

	val mk_rat_add	: term * term -> term
	val mk_rat_sub	: term * term -> term
	val mk_rat_mul	: term * term -> term
	val mk_rat_div	: term * term -> term

	val dest_rat_nmr	: term -> term
	val dest_rat_dnm	: term -> term
	val dest_rat_sgn	: term -> term

	val dest_rat_ainv	: term -> term
	val dest_rat_minv	: term -> term

	val dest_rat_add	: term -> term * term
	val dest_rat_sub	: term -> term * term
	val dest_rat_mul	: term -> term * term
	val dest_rat_div	: term -> term * term

	val dest_rat_les	: term -> term * term
	val dest_rat_gre	: term -> term * term
	val dest_rat_leq	: term -> term * term
	val dest_rat_geq	: term -> term * term

	val is_rat_nmr	: term -> bool
	val is_rat_dnm	: term -> bool
	val is_rat_sgn	: term -> bool

	val is_rat_ainv	: term -> bool
	val is_rat_minv	: term -> bool

	val is_rat_add	: term -> bool
	val is_rat_sub	: term -> bool
	val is_rat_mul	: term -> bool
	val is_rat_div	: term -> bool

	val is_rat_les	: term -> bool
	val is_rat_gre	: term -> bool
	val is_rat_leq	: term -> bool
	val is_rat_geq	: term -> bool

	val list_rat_add : term list -> term
	val list_rat_mul : term list -> term

	val strip_rat_add : term -> term list
	val strip_rat_mul : term -> term list

end;
