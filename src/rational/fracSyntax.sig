signature fracSyntax =
sig
	type term = Term.term
	type hol_type = Abbrev.hol_type

	val frac	: hol_type

	val frac_0_tm	: term
	val frac_1_tm	: term

	val frac_nmr_tm	: term
	val frac_dnm_tm	: term
	val frac_sgn_tm	: term
	val frac_ainv_tm	: term
	val frac_minv_tm	: term
	val frac_add_tm	: term
	val frac_sub_tm	: term
	val frac_mul_tm	: term
	val frac_div_tm	: term

	val mk_frac_nmr	: term -> term
	val mk_frac_dnm	: term -> term
	val mk_frac_sgn	: term -> term
	val mk_frac_ainv	: term -> term
	val mk_frac_minv	: term -> term
	val mk_frac_add	: term * term -> term
	val mk_frac_sub	: term * term -> term
	val mk_frac_mul	: term * term -> term
	val mk_frac_div	: term * term -> term

	val dest_frac_nmr	: term -> term
	val dest_frac_dnm	: term -> term
	val dest_frac_sgn	: term -> term
	val dest_frac_ainv	: term -> term
	val dest_frac_minv	: term -> term
	val dest_frac_add	: term -> term * term
	val dest_frac_sub	: term -> term * term
	val dest_frac_mul	: term -> term * term
	val dest_frac_div	: term -> term * term

	val is_frac_nmr	: term -> bool
	val is_frac_dnm	: term -> bool
	val is_frac_sgn	: term -> bool
	val is_frac_ainv	: term -> bool
	val is_frac_minv	: term -> bool
	val is_frac_add	: term -> bool
	val is_frac_sub	: term -> bool
	val is_frac_mul	: term -> bool
	val is_frac_div	: term -> bool

end;
