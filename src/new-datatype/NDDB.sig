signature NDDB =
sig

include Abbrev

type rich_type = {
  inj_pair : thm,
  ret_map  : thm,
  all_tm   : term,
  all_thm  : thm,
  all_map  : thm,
  all_T    : thm,
  all_mono : thm
}

val types : (string list * rich_type list) ref

val constantly_rich : rich_type

val    sum_all_def : thm
val   prod_all_def : thm
val   list_all_def : thm
val option_all_def : thm
val    fun_all_def : thm

val inj_pair_tm : term
val        J_tm : term

val inj_constr_thm : thm
val   some_inj_thm : thm
val      k_inj_thm : thm

val DEEP_SYM : thm -> thm

end
