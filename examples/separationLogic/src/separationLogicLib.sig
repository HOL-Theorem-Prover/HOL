signature separationLogicLib =
sig


val bool_eq_imp_CONV : Abbrev.conv;
val bool_neg_pair_CONV : Abbrev.conv;

val bool_eq_imp_ss : simpLib.ssfrag;
val bool_neg_pair_ss : simpLib.ssfrag;

end

