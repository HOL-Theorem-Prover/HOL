structure pred_setSyntax :> pred_setSyntax =
struct

local open pred_setTheory in end;

open HolKernel Abbrev;

(* Dealt with specially *)

val in_tm       = prim_mk_const{Name = "IN",       Thy = "bool"}

val diff_tm     = prim_mk_const{Name = "DIFF",     Thy = "pred_set"}
val compl_tm    = prim_mk_const{Name = "COMPL",    Thy = "pred_set"}
val card_tm     = prim_mk_const{Name = "CARD",     Thy = "pred_set"}
val delete_tm   = prim_mk_const{Name = "DELETE",   Thy = "pred_set"}
val choice_tm   = prim_mk_const{Name = "CHOICE",   Thy = "pred_set"}
val insert_tm   = prim_mk_const{Name = "INSERT",   Thy = "pred_set"}
val inj_tm      = prim_mk_const{Name = "INJ",      Thy = "pred_set"}
val bij_tm      = prim_mk_const{Name = "BIJ",      Thy = "pred_set"}
val inter_tm    = prim_mk_const{Name = "INTER",    Thy = "pred_set"}
val infinite_tm = prim_mk_const{Name = "INFINITE", Thy = "pred_set"}
val gspec_tm    = prim_mk_const{Name = "GSPEC",    Thy = "pred_set"}
val surj_tm     = prim_mk_const{Name = "SURJ",     Thy = "pred_set"}
val univ_tm     = prim_mk_const{Name = "UNIV",     Thy = "pred_set"}
val image_tm    = prim_mk_const{Name = "IMAGE",    Thy = "pred_set"}
val finite_tm   = prim_mk_const{Name = "FINITE",   Thy = "pred_set"}
val count_tm    = prim_mk_const{Name = "count",    Thy = "pred_set"}
val sing_tm     = prim_mk_const{Name = "SING",     Thy = "pred_set"}
val rinv_tm     = prim_mk_const{Name = "RINV",     Thy = "pred_set"}
val rest_tm     = prim_mk_const{Name = "REST",     Thy = "pred_set"}
val subset_tm   = prim_mk_const{Name = "SUBSET",   Thy = "pred_set"}
val psubset_tm  = prim_mk_const{Name = "PSUBSET",  Thy = "pred_set"}
val disjoint_tm = prim_mk_const{Name = "DISJOINT", Thy = "pred_set"}
val linv_tm     = prim_mk_const{Name = "LINV",     Thy = "pred_set"}
val union_tm    = prim_mk_const{Name = "UNION",    Thy = "pred_set"}
val empty_tm    = prim_mk_const{Name = "EMPTY",    Thy = "pred_set"}
val bigunion_tm = prim_mk_const{Name = "BIGUNION", Thy = "pred_set"}
val cross_tm    = prim_mk_const{Name = "CROSS",    Thy = "pred_set"};


fun mk_in (x,s) = list_mk_comb (inst [alpha |-> type_of x] in_tm, [x,s])

fun strip_set e =
 let fun strip tm = 
      let val (_,[h,t]) = (assert (same_const insert_tm) ## I) (strip_comb tm)
      in h::strip t
      end 
      handle HOL_ERR _ 
      => if same_const tm empty_tm then [] else raise e
 in strip
 end;

end
