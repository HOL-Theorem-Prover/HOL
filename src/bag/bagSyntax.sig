signature bagSyntax =
sig
   include Abbrev

  val EMPTY_BAG_tm : term
  val BAG_DIFF_tm : term
  val SUB_BAG_tm : term
  val BAG_INSERT_tm : term
  val BAG_UNION_tm : term
  val BAG_IMAGE_tm : term
  val BAG_CARD_tm : term
  val BAG_ALL_DISTINCT_tm : term
  val BAG_EVERY_tm : term

  val is_bag_ty : hol_type -> bool
  val bag_ty : hol_type

  val base_type : term -> hol_type
  val list_mk_union : term list -> term
  val mk_diff : term * term -> term
  val mk_sub_bag : term * term -> term
  val dest_sub_bag : term -> term * term
  val is_sub_bag : term -> bool
  val is_diff : term -> bool
  val dest_diff : term -> term * term
  val mk_union : term * term -> term
  val list_mk_insert : term list * term -> term
  val mk_insert : term * term -> term
  val dest_union : term -> term * term
  val strip_union : term -> term list
  val is_insert : term -> bool
  val dest_insert : term -> term * term
  val is_union : term -> bool
  val mk_image : term * term -> term
  val dest_image : term -> term * term
  val is_image : term -> bool
  val is_empty : term -> bool
  val mk_all_distinct : term -> term
  val dest_all_distinct : term -> term
  val is_all_distinct : term -> bool
  val mk_card : term -> term
  val dest_card : term -> term
  val is_card : term -> bool
  val mk_every : term * term -> term
  val dest_every : term -> term * term
  val is_every : term -> bool

  val mk_bag : term list * hol_type -> term
  val strip_insert : term -> term list * term
  val dest_bag : term -> term list * hol_type

end
