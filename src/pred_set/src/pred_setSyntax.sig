signature pred_setSyntax =
sig
  include Abbrev

  val mk_set_type : hol_type -> hol_type
  val dest_set_type : hol_type -> hol_type
  val is_set_type : hol_type -> bool

  val eltype : term -> hol_type

  val in_tm       : term
  val empty_tm    : term
  val univ_tm     : term
  val insert_tm   : term
  val inter_tm    : term
  val union_tm    : term
  val diff_tm     : term
  val delete_tm   : term
  val gspec_tm    : term
  val compl_tm    : term
  val card_tm     : term
  val image_tm    : term
  val finite_tm   : term
  val sing_tm     : term
  val subset_tm   : term
  val pow_tm      : term
  val psubset_tm  : term
  val disjoint_tm : term
  val bigunion_tm : term
  val biginter_tm : term
  val cross_tm    : term
  val count_tm    : term
  val max_set_tm  : term
  val min_set_tm  : term
  val sum_image_tm: term
  val sum_set_tm  : term
  val choice_tm   : term
  val rest_tm     : term
  val inj_tm      : term
  val surj_tm     : term
  val bij_tm      : term
  val linv_tm     : term
  val rinv_tm     : term

  val mk_in       : term * term -> term
  val mk_empty    : hol_type -> term
  val mk_univ    : hol_type -> term
  val mk_insert   : term * term -> term
  val prim_mk_set : term list * hol_type -> term
  val mk_set      : term list -> term
  val mk_inter    : term * term -> term
  val mk_union    : term * term -> term
  val mk_diff     : term * term -> term
  val mk_delete   : term * term -> term
  val prim_mk_set_spec : term * term * term list -> term
  val mk_set_spec : term * term -> term
  val mk_compl    : term -> term
  val mk_card     : term -> term
  val mk_image    : term * term -> term
  val mk_finite   : term -> term
  val mk_infinite : term -> term
  val mk_sing     : term -> term
  val mk_subset   : term * term -> term
  val mk_psubset  : term * term -> term
  val mk_pow      : term -> term
  val mk_disjoint : term * term -> term
  val mk_bigunion : term -> term
  val mk_biginter : term -> term
  val list_mk_bigunion : term list -> term
  val list_mk_biginter : term list -> term
  val mk_cross    : term * term -> term
  val mk_count    : term -> term
  val mk_max_set  : term -> term
  val mk_min_set  : term -> term
  val mk_sum_image : term * term -> term
  val mk_sum_set  : term -> term
  val mk_choice   : term -> term
  val mk_rest     : term -> term
  val mk_inj      : term * term * term-> term
  val mk_surj     : term * term * term-> term
  val mk_bij      : term * term * term-> term
  val mk_linv     : term * term * term-> term
  val mk_rinv     : term * term * term-> term

  val dest_in     : term -> term * term
  val dest_empty  : term -> hol_type
  val dest_univ   : term -> hol_type
  val dest_insert : term -> term * term
  val strip_set   : term -> term list
  val dest_inter  : term -> term * term
  val dest_union  : term -> term * term
  val dest_diff   : term -> term * term
  val dest_delete : term -> term * term
  val dest_set_spec : term -> term * term
  val dest_compl  : term -> term
  val dest_card   : term -> term
  val dest_image  : term -> term * term
  val dest_finite : term -> term
  val dest_infinite : term -> term
  val dest_sing   : term -> term
  val dest_subset : term -> term * term
  val dest_psubset : term -> term * term
  val dest_pow    : term -> term
  val dest_disjoint : term -> term * term
  val dest_bigunion : term -> term
  val dest_biginter : term -> term
  val strip_bigunion : term -> term list
  val strip_biginter : term -> term list
  val dest_cross  : term -> term * term
  val dest_count  : term -> term
  val dest_max_set : term -> term
  val dest_min_set : term -> term
  val dest_sum_image : term -> term * term
  val dest_sum_set : term -> term
  val dest_choice : term -> term
  val dest_rest   : term -> term
  val dest_inj    : term -> term * term * term
  val dest_surj   : term -> term * term * term
  val dest_bij    : term -> term * term * term
  val dest_linv   : term -> term * term * term
  val dest_rinv   : term -> term * term * term

  val is_in       : term -> bool
  val is_empty    : term -> bool
  val is_univ     : term -> bool
  val is_insert   : term -> bool
  val is_inter    : term -> bool
  val is_union    : term -> bool
  val is_diff     : term -> bool
  val is_delete   : term -> bool
  val is_set_spec : term -> bool
  val is_compl    : term -> bool
  val is_card     : term -> bool
  val is_image    : term -> bool
  val is_finite   : term -> bool
  val is_infinite : term -> bool
  val is_sing     : term -> bool
  val is_subset   : term -> bool
  val is_psubset  : term -> bool
  val is_pow      : term -> bool
  val is_disjoint : term -> bool
  val is_bigunion : term -> bool
  val is_biginter : term -> bool
  val is_cross    : term -> bool
  val is_count    : term -> bool
  val is_max_set  : term -> bool
  val is_min_set  : term -> bool
  val is_sum_image: term -> bool
  val is_sum_set  : term -> bool
  val is_choice   : term -> bool
  val is_rest     : term -> bool
  val is_inj      : term -> bool
  val is_surj     : term -> bool
  val is_bij      : term -> bool
  val is_linv     : term -> bool
  val is_rinv     : term -> bool

end
