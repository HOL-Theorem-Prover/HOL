signature sptreeSyntax =
sig

   include Abbrev

   val remove_sptree_printer : unit -> unit
   val temp_add_sptree_printer : unit -> unit

   val dest_sptree_ty : hol_type -> hol_type
   val mk_sptree_ty : hol_type -> hol_type
   val sptree_ty_of : term -> hol_type

   val fromList : term list -> term
   val fromAList : (Arbnum.num * term) list -> term

   val bn_tm : term
   val bs_tm : term
   val delete_tm : term
   val difference_tm : term
   val domain_tm : term
   val foldi_tm : term
   val fromAList_tm : term
   val fromList_tm : term
   val insert_tm : term
   val inter_eq_tm : term
   val inter_tm : term
   val ln_tm : term
   val lookup_tm : term
   val ls_tm : term
   val mk_bn_tm : term
   val mk_bs_tm : term
   val mk_wf_tm : term
   val size_tm : term
   val toAList_tm : term
   val toList_tm : term
   val union_tm : term
   val wf_tm : term

   val dest_bn : term -> term * term
   val dest_bs : term -> term * term * term
   val dest_delete : term -> term * term
   val dest_difference : term -> term * term
   val dest_domain : term -> term
   val dest_foldi : term -> term * term * term * term
   val dest_fromAList : term -> term
   val dest_fromList : term -> term
   val dest_insert : term -> term * term * term
   val dest_inter : term -> term * term
   val dest_inter_eq : term -> term * term
   val dest_ln : term -> hol_type
   val dest_lookup : term -> term * term
   val dest_ls : term -> term
   val dest_mk_bn : term -> term * term
   val dest_mk_bs : term -> term * term * term
   val dest_mk_wf : term -> term
   val dest_size : term -> term
   val dest_toAList : term -> term
   val dest_toList : term -> term
   val dest_union : term -> term * term
   val dest_wf : term -> term

   val is_bn : term -> bool
   val is_bs : term -> bool
   val is_delete : term -> bool
   val is_difference : term -> bool
   val is_domain : term -> bool
   val is_foldi : term -> bool
   val is_fromAList : term -> bool
   val is_fromList : term -> bool
   val is_insert : term -> bool
   val is_inter : term -> bool
   val is_inter_eq : term -> bool
   val is_ln : term -> bool
   val is_lookup : term -> bool
   val is_ls : term -> bool
   val is_mk_bn : term -> bool
   val is_mk_bs : term -> bool
   val is_mk_wf : term -> bool
   val is_size : term -> bool
   val is_toAList : term -> bool
   val is_toList : term -> bool
   val is_union : term -> bool
   val is_wf : term -> bool

   val mk_bn : term * term -> term
   val mk_bs : term * term * term -> term
   val mk_delete : term * term -> term
   val mk_difference : term * term -> term
   val mk_domain : term -> term
   val mk_foldi : term * term * term * term -> term
   val mk_fromAList : term -> term
   val mk_fromList : term -> term
   val mk_insert : term * term * term -> term
   val mk_inter : term * term -> term
   val mk_inter_eq : term * term -> term
   val mk_ln : hol_type -> term
   val mk_lookup : term * term -> term
   val mk_ls : term -> term
   val mk_mk_bn : term * term -> term
   val mk_mk_bs : term * term * term -> term
   val mk_mk_wf : term -> term
   val mk_size : term -> term
   val mk_toAList : term -> term
   val mk_toList : term -> term
   val mk_union : term * term -> term
   val mk_wf : term -> term

end
