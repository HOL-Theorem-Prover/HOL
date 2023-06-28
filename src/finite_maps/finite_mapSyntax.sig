signature finite_mapSyntax =
sig

  include Abbrev

  val dest_fmap_ty : hol_type -> hol_type * hol_type
  val mk_fmap_ty : hol_type * hol_type -> hol_type
  val is_fmap_ty : hol_type -> bool

  val drestrict_tm : term
  val fapply_tm : term
  val fcard_tm : term
  val fdiff_tm : term
  val fdom_tm : term
  val fempty_tm : term
  val fevery_tm : term
  val frange_tm : term
  val flookup_tm : term
  val fmap_map2_tm : term
  val fmerge_tm : term
  val fun_fmap_tm : term
  val funion_tm : term
  val fupdate_list_tm : term
  val fupdate_tm : term
  val rrestrict_tm : term

  val mk_drestrict : term * term -> term
  val mk_fapply : term * term -> term
  val mk_fcard : term -> term
  val mk_fdiff : term * term -> term
  val mk_fdom : term -> term
  val mk_fempty : hol_type * hol_type -> term
  val mk_fevery : term * term -> term
  val mk_frange : term -> term
  val mk_flookup : term * term -> term
  val mk_fmap_map2 : term * term -> term
  val mk_fmerge : term * term * term -> term
  val mk_fun_fmap : term * term -> term
  val mk_funion : term * term -> term
  val mk_fupdate : term * term -> term
  val mk_fupdate_list : term * term -> term
  val mk_rrestrict : term * term -> term

  val dest_drestrict : term -> term * term
  val dest_fapply : term -> term * term
  val dest_fcard : term -> term
  val dest_fdiff : term -> term * term
  val dest_fdom : term -> term
  val dest_fempty : term -> hol_type * hol_type
  val dest_fevery : term -> term * term
  val dest_frange : term -> term
  val dest_flookup : term -> term * term
  val dest_fmap_map2 : term -> term * term
  val dest_fmerge : term -> term * term * term
  val dest_fun_fmap : term -> term * term
  val dest_funion : term -> term * term
  val dest_fupdate : term -> term * term
  val dest_fupdate_list : term -> term * term
  val dest_rrestrict : term -> term * term

  val is_drestrict : term -> bool
  val is_fapply : term -> bool
  val is_fcard : term -> bool
  val is_fdiff : term -> bool
  val is_fdom : term -> bool
  val is_fempty : term -> bool
  val is_fevery : term -> bool
  val is_frange : term -> bool
  val is_flookup : term -> bool
  val is_fmap_map2 : term -> bool
  val is_fmerge : term -> bool
  val is_fun_fmap : term -> bool
  val is_funion : term -> bool
  val is_fupdate : term -> bool
  val is_fupdate_list : term -> bool
  val is_rrestrict : term -> bool

  val list_mk_fupdate : term * term list -> term
  val strip_fupdate : term -> term * term list

end
