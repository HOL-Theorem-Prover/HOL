structure rich_listSyntax :> rich_listSyntax =
struct

 open HolKernel Abbrev
 local open rich_listTheory in end;

val ERR = mk_HOL_ERR "rich_listSyntax";

(*---------------------------------------------------------------------------
    Constants
 ---------------------------------------------------------------------------*)

fun rich_const s = prim_mk_const {Name = s, Thy = "rich_list"}

val and_el_tm     = rich_const "AND_EL"
val butlastn_tm   = rich_const "BUTLASTN"
val ell_tm        = rich_const "ELL"
val is_sublist_tm = rich_const "IS_SUBLIST"
val is_suffix_tm  = rich_const "IS_SUFFIX"
val lastn_tm      = rich_const "LASTN"
val or_el_tm      = rich_const "OR_EL"
val prefix_tm     = rich_const "PREFIX"
val replicate_tm  = rich_const "REPLICATE"
val scanl_tm      = rich_const "SCANL"
val scanr_tm      = rich_const "SCANR"
val seg_tm        = rich_const "SEG"
val splitp_tm     = rich_const "SPLITP"
val suffix_tm     = rich_const "SUFFIX"
val unzip_fst_tm  = rich_const "UNZIP_FST"
val unzip_snd_tm  = rich_const "UNZIP_SND"

(*---------------------------------------------------------------------------
    Constructor functions
 ---------------------------------------------------------------------------*)

fun eltype l = listSyntax.dest_list_type (type_of l)

fun mk_and_el l =
  mk_comb(and_el_tm,l)
  handle HOL_ERR _ => raise ERR "mk_and_el" ""

fun mk_butlastn (n,l) =
  list_mk_comb (inst [alpha |-> eltype l] butlastn_tm, [n,l])
  handle HOL_ERR _ => raise ERR "mk_butlastn" ""

fun mk_ell (n,l) =
  list_mk_comb (inst [alpha |-> eltype l] ell_tm, [n,l])
  handle HOL_ERR _ => raise ERR "mk_ell" ""

fun mk_is_sublist (l1,l2) =
  list_mk_comb (inst [alpha |-> eltype l1] is_sublist_tm, [l1,l2])
  handle HOL_ERR _ => raise ERR "mk_is_sublist" ""

fun mk_is_suffix (l1,l2) =
  list_mk_comb (inst [alpha |-> eltype l1] is_suffix_tm, [l1,l2])
  handle HOL_ERR _ => raise ERR "mk_is_suffix" ""

fun mk_lastn (n,l) =
  list_mk_comb (inst [alpha |-> eltype l] lastn_tm, [n,l])
  handle HOL_ERR _ => raise ERR "mk_lastn" ""

fun mk_or_el l =
  mk_comb(or_el_tm,l)
  handle HOL_ERR _ => raise ERR "mk_or_el" ""

fun mk_prefix (p,l) =
  list_mk_comb (inst [alpha |-> eltype l] prefix_tm, [p,l])
  handle HOL_ERR _ => raise ERR "mk_prefix" ""

fun mk_replicate (n,m) =
  list_mk_comb (inst [alpha |-> type_of m] replicate_tm, [n,m])
  handle HOL_ERR _ => raise ERR "mk_replicate" ""

fun mk_scanl (f,e,l) =
  list_mk_comb (inst [alpha |-> eltype l, beta |-> type_of e] scanl_tm, [f,e,l])
  handle HOL_ERR _ => raise ERR "mk_scanl" ""

fun mk_scanr (f,e,l) =
  list_mk_comb (inst [alpha |-> eltype l, beta |-> type_of e] scanr_tm, [f,e,l])
  handle HOL_ERR _ => raise ERR "mk_scanr" ""

fun mk_seg (n,m,l) =
  list_mk_comb (inst [alpha |-> eltype l] seg_tm, [n,m,l])
  handle HOL_ERR _ => raise ERR "mk_seg" ""

fun mk_splitp (p,l) =
  list_mk_comb (inst [alpha |-> eltype l] splitp_tm, [p,l])
  handle HOL_ERR _ => raise ERR "mk_splitp" ""

fun mk_suffix (p,l) =
  list_mk_comb (inst [alpha |-> eltype l] suffix_tm, [p,l])
  handle HOL_ERR _ => raise ERR "mk_suffix" ""

fun mk_unzip_fst l =
  let val (a,b) = pairSyntax.dest_prod (eltype l) in
    mk_comb (inst [alpha |-> a, beta |-> b] unzip_fst_tm, l)
  end handle HOL_ERR _ => raise ERR "mk_unzip_fst" ""

fun mk_unzip_snd l =
  let val (a,b) = pairSyntax.dest_prod (eltype l) in
    mk_comb (inst [alpha |-> a, beta |-> b] unzip_snd_tm, l)
  end handle HOL_ERR _ => raise ERR "mk_unzip_snd" ""

(*---------------------------------------------------------------------------
    Destructors
 ---------------------------------------------------------------------------*)

val dest_and_el   = dest_monop and_el_tm   (ERR "dest_and_el"   "not AND_EL")
val dest_butlastn = dest_binop butlastn_tm (ERR "dest_butlastn" "not BUTLASTN")
val dest_ell      = dest_binop ell_tm      (ERR "dest_ell"      "not ELL")

val dest_is_sublist =
  dest_binop is_sublist_tm (ERR "dest_is_sublist" "not IS_SUBLIST")

val dest_is_suffix =
  dest_binop is_suffix_tm (ERR "dest_is_suffix" "not IS_SUFFIX")

val dest_lastn    = dest_binop lastn_tm    (ERR "dest_lastn"    "not LASTN")
val dest_or_el    = dest_monop or_el_tm    (ERR "dest_or_el"    "not OR_EL")
val dest_prefix   = dest_binop prefix_tm   (ERR "dest_prefix"   "not PREFIX")

val dest_replicate =
  dest_binop replicate_tm (ERR "dest_replicate" "not REPLICATE")

val dest_scanl    = dest_triop scanl_tm    (ERR "dest_scanl"    "not SCANL")
val dest_scanr    = dest_triop scanr_tm    (ERR "dest_scanr"    "not SCANR")
val dest_seg      = dest_triop seg_tm      (ERR "dest_seg"      "not SEG")
val dest_splitp   = dest_binop splitp_tm   (ERR "dest_splito"   "not SPLITP")
val dest_suffix   = dest_binop suffix_tm   (ERR "dest_suffix"   "not SUFFIX")

val dest_unzip_fst =
  dest_monop unzip_fst_tm (ERR "dest_unzip_fst" "not UNZIP_FST")

val dest_unzip_snd =
  dest_monop unzip_snd_tm (ERR "dest_unzip_snd" "not UNZIP_SND")

(*---------------------------------------------------------------------------
    Queries
 ---------------------------------------------------------------------------*)

val is_and_el     = can dest_and_el
val is_butlastn   = can dest_butlastn
val is_ell        = can dest_ell
val is_is_sublist = can dest_is_sublist
val is_is_suffix  = can dest_is_suffix
val is_lastn      = can dest_lastn
val is_or_el      = can dest_or_el
val is_prefix     = can dest_prefix
val is_replicate  = can dest_replicate
val is_scanl      = can dest_scanl
val is_scanr      = can dest_scanr
val is_seg        = can dest_seg
val is_splitp     = can dest_splitp
val is_suffix     = can dest_suffix
val is_unzip_fst  = can dest_unzip_fst
val is_unzip_snd  = can dest_unzip_snd

end
