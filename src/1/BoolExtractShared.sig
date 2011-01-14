signature BoolExtractShared =
sig

include Abbrev

val dest_neg_eq : term -> term * term
val is_neg_eq : term -> bool
val mk_neg___idempot : term -> term
val eq_sym_aconv : term -> term -> bool


val BOOL_EQ_IMP_CONV : conv;
val BOOL_NEG_PAIR_CONV : conv;
val BOOL_EXTRACT_SHARED_CONV : conv;

val BOOL_EQ_IMP_convdata : simpfrag.convdata
val BOOL_EXTRACT_SHARED_convdata : simpfrag.convdata;
val BOOL_NEG_PAIR_convdata : simpfrag.convdata;


end

