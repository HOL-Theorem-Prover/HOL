structure rich_listSyntax :> rich_listSyntax =
struct

 open HolKernel Abbrev
 local open rich_listTheory in end;

(*---------------------------------------------------------------------------
    Syntax functions for rich_list
 ---------------------------------------------------------------------------*)

val monop =
   HolKernel.syntax_fns "rich_list" 1 HolKernel.dest_monop HolKernel.mk_monop

val binop =
   HolKernel.syntax_fns "rich_list" 2 HolKernel.dest_binop HolKernel.mk_binop

val triop =
   HolKernel.syntax_fns "rich_list" 3 HolKernel.dest_triop HolKernel.mk_triop

val (and_el_tm, mk_and_el, dest_and_el, is_and_el) = monop "AND_EL"
val (count_list_tm, mk_count_list, dest_count_list, is_count_list) =
   monop "COUNT_LIST"
val (or_el_tm, mk_or_el, dest_or_el, is_or_el) = monop "OR_EL"
val (unzip_fst_tm, mk_unzip_fst, dest_unzip_fst, is_unzip_fst) =
   monop "UNZIP_FST"
val (unzip_snd_tm, mk_unzip_snd, dest_unzip_snd, is_unzip_snd) =
   monop "UNZIP_SND"

val (ell_tm, mk_ell, dest_ell, is_ell) = binop "ELL"
val (is_sublist_tm, mk_is_sublist, dest_is_sublist, is_is_sublist) =
   binop "IS_SUBLIST"
val (is_suffix_tm, mk_is_suffix, dest_is_suffix, is_is_suffix) =
   binop "IS_SUFFIX"
val (lastn_tm, mk_lastn, dest_lastn, is_lastn) = binop "LASTN"
val (butlastn_tm, mk_butlastn, dest_butlastn, is_butlastn) = binop "BUTLASTN"
val (prefix_tm, mk_prefix, dest_prefix, is_prefix) = binop "PREFIX"
val (replicate_tm, mk_replicate, dest_replicate, is_replicate) =
   binop "REPLICATE"
val (list_elem_count_tm, mk_list_elem_count, dest_list_elem_count,
     is_list_elem_count) = binop "LIST_ELEM_COUNT"
val (suffix_tm, mk_suffix, dest_suffix, is_suffix) = binop "SUFFIX"
val (splitp_tm, mk_splitp, dest_splitp, is_splitp) = binop "SPLITP"
val (splitl_tm, mk_splitl, dest_splitl, is_splitl) = binop "SPLITL"
val (splitr_tm, mk_splitr, dest_splitr, is_splitr) = binop "SPLITR"

val (scanl_tm, mk_scanl, dest_scanl, is_scanl) = triop "SCANL"
val (scanr_tm, mk_scanr, dest_scanr, is_scanr) = triop "SCANR"
val (seg_tm, mk_seg, dest_seg, is_seg) = triop "SEG"

end
