signature listSyntax = 
sig
  include Abbrev

  val mk_list_type   : hol_type -> hol_type
  val dest_list_type : hol_type -> hol_type
  val is_list_type   : hol_type -> bool

  val eltype         : term -> hol_type

  val nil_tm         : term
  val cons_tm        : term
  val null_tm        : term
  val hd_tm          : term
  val tl_tm          : term
  val append_tm      : term
  val flat_tm        : term
  val length_tm      : term
  val map_tm         : term
  val map2_tm        : term
  val mem_tm         : term
  val filter_tm      : term
  val foldr_tm       : term
  val foldl_tm       : term
  val every_tm       : term
  val exists_tm      : term
  val el_tm          : term
  val zip_tm         : term
  val unzip_tm       : term
  val sum_tm         : term
  val reverse_tm     : term
  val list_case_tm   : term
  val last_tm        : term
  val front_tm       : term
  val all_distinct_tm: term

  val mk_nil         : hol_type -> term
  val mk_cons        : term * term -> term
  val mk_null        : term -> term
  val mk_hd          : term -> term
  val mk_tl          : term -> term
  val mk_append      : term * term -> term
  val mk_flat        : term -> term
  val mk_length      : term -> term
  val mk_map         : term * term -> term
  val mk_map2        : term * term * term -> term
  val mk_mem         : term * term -> term
  val mk_filter      : term * term -> term
  val mk_foldr       : term * term * term -> term
  val mk_foldl       : term * term * term -> term
  val mk_every       : term * term -> term
  val mk_exists      : term * term -> term
  val mk_el          : term * term -> term
  val mk_zip         : term * term -> term
  val mk_unzip       : term -> term
  val mk_sum         : term -> term
  val mk_reverse     : term -> term
  val mk_list_case   : term * term * term -> term
  val mk_last        : term -> term
  val mk_front       : term -> term
  val mk_all_distinct: term -> term
  val mk_list        : term list * hol_type -> term

  val dest_nil       : term -> hol_type
  val dest_cons      : term -> term * term
  val dest_null      : term -> term
  val dest_hd        : term -> term
  val dest_tl        : term -> term
  val dest_append    : term -> term * term
  val dest_flat      : term -> term
  val dest_length    : term -> term
  val dest_map       : term -> term * term
  val dest_map2      : term -> term * term * term
  val dest_mem       : term -> term * term
  val dest_filter    : term -> term * term
  val dest_foldr     : term -> term * term * term
  val dest_foldl     : term -> term * term * term
  val dest_every     : term -> term * term
  val dest_exists    : term -> term * term
  val dest_el        : term -> term * term
  val dest_zip       : term -> term * term
  val dest_unzip     : term -> term
  val dest_sum       : term -> term
  val dest_reverse   : term -> term
  val dest_list_case : term -> term * term * term
  val dest_last        : term -> term
  val dest_front       : term -> term
  val dest_all_distinct: term -> term
  val dest_list      : term -> term list * hol_type

  val is_nil         : term -> bool
  val is_cons        : term -> bool
  val is_null        : term -> bool
  val is_hd          : term -> bool
  val is_tl          : term -> bool
  val is_append      : term -> bool
  val is_flat        : term -> bool
  val is_length      : term -> bool
  val is_map         : term -> bool
  val is_map2        : term -> bool
  val is_mem         : term -> bool
  val is_filter      : term -> bool
  val is_foldr       : term -> bool
  val is_foldl       : term -> bool
  val is_every       : term -> bool
  val is_exists      : term -> bool
  val is_el          : term -> bool
  val is_zip         : term -> bool
  val is_unzip       : term -> bool
  val is_sum         : term -> bool
  val is_reverse     : term -> bool
  val is_list_case   : term -> bool
  val is_last        : term -> bool
  val is_front       : term -> bool
  val is_all_distinct: term -> bool
  val is_list        : term -> bool

  val lift_list      : hol_type -> ('a -> term) -> 'a list -> term

end
