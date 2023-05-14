signature cvSyntax =
sig

  include Abbrev;

  val cv : hol_type;

  val cv_pair_tm : term;
  val cv_num_tm : term;
  val cv_fst_tm : term;
  val cv_snd_tm : term;
  val cv_ispair_tm : term;
  val cv_add_tm : term;
  val cv_sub_tm : term;
  val cv_mul_tm : term;
  val cv_div_tm : term;
  val cv_mod_tm : term;
  val cv_lt_tm : term;
  val cv_if_tm : term;
  val cv_eq_tm : term;
  val safediv_tm : term;
  val safemod_tm : term;

  val mk_cv_pair : term * term -> term;
  val mk_cv_num : term -> term;
  val mk_cv_fst : term -> term;
  val mk_cv_snd : term -> term;
  val mk_cv_ispair : term -> term;
  val mk_cv_add : term * term -> term;
  val mk_cv_sub : term * term -> term;
  val mk_cv_mul : term * term -> term;
  val mk_cv_div : term * term -> term;
  val mk_cv_mod : term * term -> term;
  val mk_cv_lt : term * term -> term;
  val mk_cv_if : term * term * term -> term;
  val mk_cv_eq : term * term -> term;
  val mk_safediv : term -> term;
  val mk_safemod : term -> term;

  val dest_cv_pair : term -> term * term;
  val dest_cv_num : term -> term;
  val dest_cv_fst : term -> term;
  val dest_cv_snd : term -> term;
  val dest_cv_ispair : term -> term;
  val dest_cv_add : term -> term * term;
  val dest_cv_sub : term -> term * term;
  val dest_cv_mul : term -> term * term;
  val dest_cv_div : term -> term * term;
  val dest_cv_mod : term -> term * term;
  val dest_cv_lt : term -> term * term;
  val dest_cv_if : term -> term * term * term;
  val dest_cv_eq : term -> term * term;
  val dest_safediv : term -> term * term;
  val dest_safemod : term -> term * term;

  val is_cv_pair : term -> bool;
  val is_cv_num : term -> bool;
  val is_cv_fst : term -> bool;
  val is_cv_snd : term -> bool;
  val is_cv_ispair : term -> bool;
  val is_cv_add : term -> bool;
  val is_cv_sub : term -> bool;
  val is_cv_mul : term -> bool;
  val is_cv_div : term -> bool;
  val is_cv_mod : term -> bool;
  val is_cv_lt : term -> bool;
  val is_cv_if : term -> bool;
  val is_cv_eq : term -> bool;
  val is_safediv : term -> bool;
  val is_safemod : term -> bool;

end (* signature *)

