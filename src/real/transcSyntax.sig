signature transcSyntax =
sig
   type term = Term.term

   val Dint_tm: term
   val acs_tm: term
   val asn_tm: term
   val atn_tm: term
   val cos_tm: term
   val division_tm: term
   val dsize_tm: term
   val exp_tm: term
   val fine_tm: term
   val gauge_tm: term
   val ln_tm: term
   val pi_tm: term
   val root_tm: term
   val rpow_tm: term
   val rsum_tm: term
   val sin_tm: term
   val sqrt_tm: term
   val tan_tm: term
   val tdiv_tm: term

   val dest_Dint: term -> term * term * term
   val dest_acs: term -> term
   val dest_asn: term -> term
   val dest_atn: term -> term
   val dest_cos: term -> term
   val dest_division: term -> term * term
   val dest_dsize: term -> term
   val dest_exp: term -> term
   val dest_fine: term -> term * term
   val dest_gauge: term -> term * term
   val dest_ln: term -> term
   val dest_root: term -> term * term
   val dest_rpow: term -> term * term
   val dest_rsum: term -> term * term
   val dest_sin: term -> term
   val dest_sqrt: term -> term
   val dest_tan: term -> term
   val dest_tdiv: term -> term * term

   val is_Dint: term -> bool
   val is_acs: term -> bool
   val is_asn: term -> bool
   val is_atn: term -> bool
   val is_cos: term -> bool
   val is_division: term -> bool
   val is_dsize: term -> bool
   val is_exp: term -> bool
   val is_fine: term -> bool
   val is_gauge: term -> bool
   val is_ln: term -> bool
   val is_root: term -> bool
   val is_rpow: term -> bool
   val is_rsum: term -> bool
   val is_sin: term -> bool
   val is_sqrt: term -> bool
   val is_tan: term -> bool
   val is_tdiv: term -> bool

   val mk_Dint: term * term * term -> term
   val mk_acs: term -> term
   val mk_asn: term -> term
   val mk_atn: term -> term
   val mk_cos: term -> term
   val mk_division: term * term -> term
   val mk_dsize: term -> term
   val mk_exp: term -> term
   val mk_fine: term * term -> term
   val mk_gauge: term * term -> term
   val mk_ln: term -> term
   val mk_root: term * term -> term
   val mk_rpow: term * term -> term
   val mk_rsum: term * term -> term
   val mk_sin: term -> term
   val mk_sqrt: term -> term
   val mk_tan: term -> term
   val mk_tdiv: term * term -> term

end
