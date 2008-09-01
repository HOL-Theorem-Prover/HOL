structure pred_setSyntax :> pred_setSyntax =
struct

local open pred_setTheory in end;

open HolKernel Abbrev;

val ERR = mk_HOL_ERR "pred_setSyntax";

(*---------------------------------------------------------------------------*)
(* Types                                                                     *)
(*---------------------------------------------------------------------------*)

fun mk_set_type ty = ty --> bool;

fun dest_set_type ty = 
 case total dom_rng ty
  of SOME(ty1,ty2) =>
       if ty2 = Type.bool then ty1 
       else raise ERR "dest_set_type" "not an instance of 'a -> bool"
   | NONE => raise ERR "dest_set_type" "not an instance of 'a -> bool";

val is_set_type  = Lib.can dest_set_type;

(*---------------------------------------------------------------------------*)
(* Get the type of the elements of a set                                     *)
(*---------------------------------------------------------------------------*)

fun eltype tm = dest_set_type (type_of tm);


(*---------------------------------------------------------------------------*)
(* Set constants. Note that "IN" is alredy defined in boolTheory.            *)
(*---------------------------------------------------------------------------*)

val in_tm       = prim_mk_const{Name = "IN",       Thy = "bool"}
val empty_tm    = prim_mk_const{Name = "EMPTY",    Thy = "pred_set"}
val univ_tm     = prim_mk_const{Name = "UNIV",     Thy = "pred_set"}
val insert_tm   = prim_mk_const{Name = "INSERT",   Thy = "pred_set"}
val inter_tm    = prim_mk_const{Name = "INTER",    Thy = "pred_set"}
val union_tm    = prim_mk_const{Name = "UNION",    Thy = "pred_set"}
val diff_tm     = prim_mk_const{Name = "DIFF",     Thy = "pred_set"}
val delete_tm   = prim_mk_const{Name = "DELETE",   Thy = "pred_set"}
val gspec_tm    = prim_mk_const{Name = "GSPEC",    Thy = "pred_set"}
val compl_tm    = prim_mk_const{Name = "COMPL",    Thy = "pred_set"}
val card_tm     = prim_mk_const{Name = "CARD",     Thy = "pred_set"}
val image_tm    = prim_mk_const{Name = "IMAGE",    Thy = "pred_set"}
val finite_tm   = prim_mk_const{Name = "FINITE",   Thy = "pred_set"}
val infinite_tm = prim_mk_const{Name = "INFINITE", Thy = "pred_set"}
val sing_tm     = prim_mk_const{Name = "SING",     Thy = "pred_set"}
val subset_tm   = prim_mk_const{Name = "SUBSET",   Thy = "pred_set"}
val psubset_tm  = prim_mk_const{Name = "PSUBSET",  Thy = "pred_set"}
val pow_tm      = prim_mk_const{Name = "POW",      Thy = "pred_set"}
val disjoint_tm = prim_mk_const{Name = "DISJOINT", Thy = "pred_set"}
val bigunion_tm = prim_mk_const{Name = "BIGUNION", Thy = "pred_set"}
val biginter_tm = prim_mk_const{Name = "BIGINTER", Thy = "pred_set"}
val cross_tm    = prim_mk_const{Name = "CROSS",    Thy = "pred_set"}
val count_tm    = prim_mk_const{Name = "count",    Thy = "pred_set"}
val max_set_tm  = prim_mk_const{Name = "MAX_SET",  Thy = "pred_set"}
val min_set_tm  = prim_mk_const{Name = "MIN_SET",  Thy = "pred_set"}
val sum_image_tm = prim_mk_const{Name="SUM_IMAGE", Thy = "pred_set"}
val sum_set_tm  = prim_mk_const{Name = "SUM_SET",  Thy = "pred_set"}
val choice_tm   = prim_mk_const{Name = "CHOICE",   Thy = "pred_set"}
val rest_tm     = prim_mk_const{Name = "REST",     Thy = "pred_set"}
val inj_tm      = prim_mk_const{Name = "INJ",      Thy = "pred_set"}
val surj_tm     = prim_mk_const{Name = "SURJ",     Thy = "pred_set"}
val bij_tm      = prim_mk_const{Name = "BIJ",      Thy = "pred_set"}
val linv_tm     = prim_mk_const{Name = "LINV",     Thy = "pred_set"}
val rinv_tm     = prim_mk_const{Name = "RINV",     Thy = "pred_set"};


(*---------------------------------------------------------------------------*)
(* Set membership                                                            *)
(*---------------------------------------------------------------------------*)

fun mk_in (x,s) = 
  list_mk_comb (inst [alpha |-> type_of x] in_tm, [x,s])
  handle HOL_ERR _ => raise ERR "mk_in" "";

val dest_in = dest_binop in_tm (ERR "dest_in" "not an IN term");

val is_in = Lib.can dest_in;

(*---------------------------------------------------------------------------*)
(* Empty set                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_empty ty = inst [alpha |-> ty] empty_tm
  handle HOL_ERR _ => raise ERR "mk_empty" "";

fun dest_empty tm =
  if same_const tm empty_tm then type_of tm
  else raise ERR "dest_empty" "not the empty set";

val is_empty = Lib.can dest_empty;

(*---------------------------------------------------------------------------*)
(* Unversal set                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_univ ty = inst [alpha |-> ty] univ_tm
  handle HOL_ERR _ => raise ERR "mk_univ" "";

fun dest_univ tm =
  if same_const tm univ_tm then type_of tm
  else raise ERR "dest_univ" "not the universal set";

val is_univ = Lib.can dest_univ;

(*---------------------------------------------------------------------------*)
(* Insertion                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_insert (tm1,tm2) =
 list_mk_comb(inst[alpha |-> type_of tm1] insert_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_insert" 
                   "element type disagrees with set type";
val dest_insert = 
  dest_binop insert_tm (ERR "dest_insert" "not an INSERT term");

val is_insert = Lib.can dest_insert;

(*---------------------------------------------------------------------------*)
(* Finitely iterated insertion                                               *)
(*---------------------------------------------------------------------------*)

fun prim_mk_set (l,ty) = 
  itlist (curry mk_insert) l (mk_empty ty)
  handle HOL_ERR _ => raise ERR "prim_mk_set" "";

fun mk_set [] = raise ERR "mk_set" "empty set"
  | mk_set (els as (h::_)) = 
      itlist (curry mk_insert) els (mk_empty (type_of h))
      handle HOL_ERR _ => raise ERR "mk_set" "";

val strip_set =
 let fun strip tm = 
      let val (h,t) = dest_insert tm
      in h::strip t
      end 
      handle HOL_ERR _ 
      => if same_const tm empty_tm then [] 
          else raise ERR "strip_set" "not an enumerated set"
 in 
   strip
 end;

(*---------------------------------------------------------------------------*)
(* Intersection                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_inter (tm1,tm2) =
 list_mk_comb(inst[alpha |-> eltype tm1] inter_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_inter" 
                   "element type disagrees with set type";
val dest_inter = 
  dest_binop inter_tm (ERR "dest_inter" "not an INTER term");

val is_inter = Lib.can dest_inter;

(*---------------------------------------------------------------------------*)
(* Union                                                                     *)
(*---------------------------------------------------------------------------*)

fun mk_union (tm1,tm2) =
 list_mk_comb(inst[alpha |-> eltype tm1] union_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_union" 
                   "element type disagrees with set type";
val dest_union = 
  dest_binop union_tm (ERR "dest_union" "not an UNION term");

val is_union = Lib.can dest_union;

(*---------------------------------------------------------------------------*)
(* Difference                                                                *)
(*---------------------------------------------------------------------------*)

fun mk_diff (tm1,tm2) =
 list_mk_comb(inst[alpha |-> eltype tm1] diff_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_diff" 
                   "element type disagrees with set type";
val dest_diff = 
  dest_binop diff_tm (ERR "dest_diff" "not an DIFF term");

val is_diff = Lib.can dest_diff;

(*---------------------------------------------------------------------------*)
(* Delete                                                                    *)
(*---------------------------------------------------------------------------*)

fun mk_delete (tm1,tm2) =
 list_mk_comb(inst[alpha |-> eltype tm1] delete_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_delete" 
                   "element type disagrees with set type";
val dest_delete = 
  dest_binop delete_tm (ERR "dest_delete" "not an DELETE term");

val is_delete = Lib.can dest_delete;

(*---------------------------------------------------------------------------*)
(* Set comprehensions                                                        *)
(*---------------------------------------------------------------------------*)

fun prim_mk_set_spec(tm1,tm2,sharedvars) =
 let val tuple = pairSyntax.list_mk_pair sharedvars
 in mk_comb(inst [alpha |-> type_of tm1,beta |-> type_of tuple]gspec_tm,
            pairSyntax.mk_pabs(tuple,pairSyntax.mk_pair(tm1,tm2)))
 end
 handle HOL_ERR _ => raise ERR "prim_mk_set_spec" "";

fun mk_set_spec (tm1,tm2) = 
 let val shared = intersect (free_vars_lr tm1) (free_vars_lr tm2)
 in prim_mk_set_spec(tm1,tm2,shared)
 end
 handle e as HOL_ERR _ => raise wrap_exn "mk_set_spec" "" e;

fun dest_set_spec tm =
 case total dest_comb tm
  of SOME (c,M) =>
      if same_const c gspec_tm
        then pairSyntax.dest_pair
               (snd (pairSyntax.dest_pabs M))
        else raise ERR "dest_set_spec" "not a set comprehension"
   | NONE => raise ERR "dest_set_spec" "not a set comprehension";

val is_set_spec = Lib.can dest_set_spec;

(*---------------------------------------------------------------------------*)
(* Complement                                                                *)
(*---------------------------------------------------------------------------*)

fun mk_compl tm =
 mk_comb(inst[alpha |-> eltype tm] compl_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_compl" "not a set?";

val dest_compl = 
  dest_monop compl_tm (ERR "dest_compl" "not a COMPL term");

val is_compl = Lib.can dest_compl;

(*---------------------------------------------------------------------------*)
(* Cardinality                                                                *)
(*---------------------------------------------------------------------------*)

fun mk_card tm =
 list_mk_comb(inst[alpha |-> eltype tm] card_tm, [tm])
  handle HOL_ERR _ => raise ERR "mk_card" "not a set?";

val dest_card = 
  dest_monop card_tm (ERR "dest_card" "not an application of CARD");

val is_card = Lib.can dest_card;

(*---------------------------------------------------------------------------*)
(* Image                                                                     *)
(*---------------------------------------------------------------------------*)

fun mk_image (tm1,tm2) =
 let val (dty,rty) = with_exn dom_rng (type_of tm1) (ERR "mk_image" "")
 in 
  list_mk_comb(inst[alpha |-> dty, beta |-> rty] image_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_image" "type disagreement"
 end

val dest_image = 
  dest_binop image_tm (ERR "dest_image" "not an IMAGE term");

val is_image = Lib.can dest_image;

(*---------------------------------------------------------------------------*)
(* Finiteness                                                                *)
(*---------------------------------------------------------------------------*)

fun mk_finite tm =
 list_mk_comb(inst[alpha |-> eltype tm] finite_tm, [tm])
  handle HOL_ERR _ => raise ERR "mk_finite" "not a set?";

val dest_finite = 
  dest_monop finite_tm (ERR "dest_finite" "not an application of FINITE");

val is_finite = Lib.can dest_finite;

(*---------------------------------------------------------------------------*)
(* Infiniteness                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_infinite tm =
 list_mk_comb(inst[alpha |-> eltype tm] infinite_tm, [tm])
  handle HOL_ERR _ => raise ERR "mk_infinite" "not a set?";

val dest_infinite = 
  dest_monop infinite_tm (ERR "dest_infinite" "not an application of INFINITE");

val is_infinite = Lib.can dest_infinite;

(*---------------------------------------------------------------------------*)
(* Singleton                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_sing tm =
 list_mk_comb(inst[alpha |-> eltype tm] sing_tm, [tm])
  handle HOL_ERR _ => raise ERR "mk_sing" "not a set?";

val dest_sing = 
  dest_monop sing_tm (ERR "dest_sing" "not an application of SING");

val is_sing = Lib.can dest_sing;

(*---------------------------------------------------------------------------*)
(* Subset                                                                    *)
(*---------------------------------------------------------------------------*)

fun mk_subset (tm1,tm2) =
 list_mk_comb(inst[alpha |-> eltype tm1] subset_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_subset" 
                   "element type disagrees with set type";
val dest_subset = 
  dest_binop subset_tm (ERR "dest_subset" "not an SUBSET term");

val is_subset = Lib.can dest_subset;

(*---------------------------------------------------------------------------*)
(* Proper subset                                                             *)
(*---------------------------------------------------------------------------*)

fun mk_psubset (tm1,tm2) =
 list_mk_comb(inst[alpha |-> eltype tm1] psubset_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_psubset" 
                   "element type disagrees with set type";
val dest_psubset = 
  dest_binop psubset_tm (ERR "dest_psubset" "not a PSUBSET term");

val is_psubset = Lib.can dest_psubset;

(*---------------------------------------------------------------------------*)
(* Power set                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_pow tm =
 list_mk_comb(inst[alpha |-> eltype tm] pow_tm, [tm])
  handle HOL_ERR _ => raise ERR "mk_pow" 
                   "element type disagrees with set type";
val dest_pow = 
  dest_monop pow_tm (ERR "dest_pow" "not a POW term");

val is_pow = Lib.can dest_pow;

(*---------------------------------------------------------------------------*)
(* Disjointness                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_disjoint (tm1,tm2) =
 list_mk_comb(inst[alpha |-> eltype tm1] disjoint_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_disjoint" 
                   "element type disagrees with set type";
val dest_disjoint = 
  dest_binop disjoint_tm (ERR "dest_disjoint" "not an DISJOINT term");

val is_disjoint = Lib.can dest_disjoint;

(*---------------------------------------------------------------------------*)
(* Big union                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_bigunion tm =
 mk_comb(inst [alpha |-> dest_set_type (eltype tm)]bigunion_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_bigunion" "not a set of sets?";

val dest_bigunion = 
  dest_monop bigunion_tm (ERR "dest_bigunion" "not an application of BIGUNION");

val is_bigunion = Lib.can dest_bigunion;

fun list_mk_bigunion sets = mk_bigunion (mk_set sets)
fun strip_bigunion tm = strip_set (dest_bigunion tm);

(*---------------------------------------------------------------------------*)
(* Big intersection                                                          *)
(*---------------------------------------------------------------------------*)

fun mk_biginter tm =
 mk_comb(inst [alpha |-> dest_set_type (eltype tm)]biginter_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_biginter" "not a set of sets?";

val dest_biginter = 
  dest_monop biginter_tm (ERR "dest_biginter" "not an application of BIGINTER");

val is_biginter = Lib.can dest_biginter;

fun list_mk_biginter sets = mk_biginter (mk_set sets)
fun strip_biginter tm = strip_set (dest_biginter tm)

(*---------------------------------------------------------------------------*)
(* Cross product                                                             *)
(*---------------------------------------------------------------------------*)

fun mk_cross (tm1,tm2) =
 list_mk_comb(inst[alpha|->eltype tm1,beta|->eltype tm2] cross_tm, [tm1,tm2])
  handle HOL_ERR _ => raise ERR "mk_cross" "" ;

val dest_cross = 
  dest_binop cross_tm (ERR "dest_cross" "not a CROSS term");

val is_cross = Lib.can dest_cross;

(*---------------------------------------------------------------------------*)
(* Set of numbers of size n                                                  *)
(*---------------------------------------------------------------------------*)

fun mk_count tm =
  mk_comb(count_tm,tm) handle HOL_ERR _ => raise ERR "mk_count" "" ;

val dest_count = 
  dest_monop count_tm (ERR "dest_count" "not a COUNT term");

val is_count = Lib.can dest_count;

(*---------------------------------------------------------------------------*)
(* Maximum of a set                                                          *)
(*---------------------------------------------------------------------------*)

fun mk_max_set tm =
 mk_comb(max_set_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_max_set" "not a set?";

val dest_max_set = 
  dest_monop max_set_tm (ERR "dest_max_set" "not an application of MAX_SET");

val is_max_set = Lib.can dest_max_set;


(*---------------------------------------------------------------------------*)
(* Minimum of a set                                                          *)
(*---------------------------------------------------------------------------*)

fun mk_min_set tm =
 mk_comb(min_set_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_min_set" "not a set?";

val dest_min_set = 
  dest_monop min_set_tm (ERR "dest_min_set" "not an application of MIN_SET");

val is_min_set = Lib.can dest_min_set;


(*---------------------------------------------------------------------------*)
(* Sum of a set under a map into numbers                                     *)
(*---------------------------------------------------------------------------*)

fun mk_sum_image (f,tm) =
 let val (dty,_) = with_exn dom_rng(type_of f) (ERR "mk_sum_image" "")
 in 
   list_mk_comb(inst [alpha |-> dty] sum_image_tm,[f,tm])
  handle HOL_ERR _ => raise ERR "mk_sum_image" ""
 end;;

val dest_sum_image = 
  dest_binop sum_image_tm (ERR "dest_sum_image" 
                               "not an application of SUM_IMAGE");

val is_sum_image = Lib.can dest_sum_image;

(*---------------------------------------------------------------------------*)
(* Sum of a set                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_sum_set tm =
 mk_comb(sum_set_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_sum_set" "not a set?";

val dest_sum_set = 
  dest_monop sum_set_tm (ERR "dest_sum_set" "not an application of SUM_SET");

val is_sum_set = Lib.can dest_sum_set;

(*---------------------------------------------------------------------------*)
(* Choose an arbitrary element                                               *)
(*---------------------------------------------------------------------------*)

fun mk_choice tm =
 mk_comb(inst[alpha |-> eltype tm]choice_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_choice" "not a set?";

val dest_choice = 
  dest_monop choice_tm (ERR "dest_choice" "not an application of CHOICE");

val is_choice = Lib.can dest_choice;

(*---------------------------------------------------------------------------*)
(* Remaining elements after a choice                                         *)
(*---------------------------------------------------------------------------*)

fun mk_rest tm =
 mk_comb(inst[alpha |-> eltype tm]rest_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_rest" "not a set?";

val dest_rest = 
  dest_monop rest_tm (ERR "dest_rest" "not an application of REST");

val is_rest = Lib.can dest_rest;


(*---------------------------------------------------------------------------*)
(* Injection                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_inj (f,s1,s2) =
 let val (dty,rty) = with_exn dom_rng(type_of f) (ERR "mk_inj" "")
 in 
   list_mk_comb(inst[alpha |-> dty, beta |-> rty]inj_tm, [f,s1,s2])
    handle HOL_ERR _ => raise ERR "mk_inj" ""
 end;

val dest_inj = 
  dest_triop inj_tm (ERR "dest_inj" "not an application of INJ");

val is_inj = Lib.can dest_inj;

(*---------------------------------------------------------------------------*)
(* Surjection                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_surj (f,s1,s2) =
 let val (dty,rty) = with_exn dom_rng(type_of f) (ERR "mk_surj" "")
 in 
   list_mk_comb(inst[alpha |-> dty, beta |-> rty]surj_tm, [f,s1,s2])
    handle HOL_ERR _ => raise ERR "mk_surj" ""
 end;

val dest_surj = 
  dest_triop surj_tm (ERR "dest_surj" "not an application of SURJ");

val is_surj = Lib.can dest_surj;

(*---------------------------------------------------------------------------*)
(* Bijection                                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_bij (f,s1,s2) =
 let val (dty,rty) = with_exn dom_rng(type_of f) (ERR "mk_bij" "")
 in 
   list_mk_comb(inst[alpha |-> dty, beta |-> rty]bij_tm, [f,s1,s2])
    handle HOL_ERR _ => raise ERR "mk_bij" ""
 end;

val dest_bij = 
  dest_triop bij_tm (ERR "dest_bij" "not an application of BIJ");

val is_bij = Lib.can dest_bij;

(*---------------------------------------------------------------------------*)
(* Left inverse                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_linv (f,s,y) =
 let val (dty,rty) = with_exn dom_rng(type_of f) (ERR "mk_linv" "")
 in 
   list_mk_comb(inst[alpha |-> dty, beta |-> rty]linv_tm, [f,s,y])
    handle HOL_ERR _ => raise ERR "mk_linv" ""
 end;

val dest_linv = 
  dest_triop linv_tm (ERR "dest_linv" "not an application of LINV");

val is_linv = Lib.can dest_linv;

(*---------------------------------------------------------------------------*)
(* Right inverse                                                             *)
(*---------------------------------------------------------------------------*)

fun mk_rinv (f,s,y) =
 let val (dty,rty) = with_exn dom_rng(type_of f) (ERR "mk_rinv" "")
 in 
   list_mk_comb(inst[alpha |-> dty, beta |-> rty]rinv_tm, [f,s,y])
    handle HOL_ERR _ => raise ERR "mk_rinv" ""
 end;

val dest_rinv = 
  dest_triop rinv_tm (ERR "dest_rinv" "not an application of RINV");

val is_rinv = Lib.can dest_rinv;

end
