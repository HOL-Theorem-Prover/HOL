structure bagSyntax :> bagSyntax =
struct

open HolKernel Parse boolLib simpLib boolSimps bagTheory;

val ERR = mk_HOL_ERR "bagLib";

val num_ty = numSyntax.num

val bag_ty = Type.alpha --> num_ty
fun is_bag_ty ty = #2 (dom_rng ty) = num_ty handle HOL_ERR _ => false

val BAG_INSERT_tm = mk_const("BAG_INSERT", alpha --> bag_ty --> bag_ty);
val BAG_UNION_tm = mk_const("BAG_UNION", bag_ty --> bag_ty --> bag_ty);
val BAG_DIFF_tm = mk_const("BAG_DIFF", bag_ty --> bag_ty --> bag_ty);
val BAG_CARD_tm = mk_const("BAG_CARD", bag_ty --> num_ty);
val EMPTY_BAG_tm = mk_const("EMPTY_BAG", bag_ty);
val SUB_BAG_tm = mk_const("SUB_BAG", bag_ty --> bag_ty --> bool);
val BAG_EQ_tm = mk_const("=", bag_ty --> bag_ty --> bool);
val BAG_IMAGE_tm = mk_const("BAG_IMAGE", 
   (Type.alpha --> Type.beta) --> (Type.alpha --> num_ty) --> 
      (Type.beta --> num_ty));
val BAG_ALL_DISTINCT_tm = mk_const("BAG_ALL_DISTINCT", bag_ty --> bool);
val BAG_EVERY_tm = mk_const("BAG_EVERY", 
   (Type.alpha --> bool) --> bag_ty --> bool)


fun base_type tm = let
  val ty = type_of tm
  val (dom,rng) = dom_rng ty
in
  if rng = num_ty then dom
  else raise ERR "bag_base_type" "term not a bag"
end

fun mk_union (tm1, tm2) = let
  val bt = base_type tm1
  val bu_tm = Term.inst [alpha |-> bt] BAG_UNION_tm
in
  list_mk_comb(bu_tm, [tm1, tm2])
end
fun mk_diff(tm1, tm2) =  let
  val bt = base_type tm1
  val bd_tm = Term.inst [alpha |-> bt] BAG_DIFF_tm
in
  list_mk_comb(bd_tm, [tm1, tm2])
end

fun dest_binop name callername tm = let
  val (f, args) = strip_comb tm
  val _ = length args = 2 orelse raise ERR callername "not a binary term"
  val (nm, _) = dest_const f
  val _ = nm = name orelse raise ERR callername ("not a "^name)
in
  (hd args, hd (tl args))
end


val dest_union = dest_binop "BAG_UNION" "dest_union"
val is_union = can dest_union
val dest_diff = dest_binop "BAG_DIFF" "dest_diff"
val is_diff = can dest_diff
fun mk_every (tm1, tm2) = list_mk_icomb(BAG_EVERY_tm, [tm1, tm2])
val dest_every = dest_binop "BAG_EVERY" "dest_every"
val is_every = can dest_every

fun list_mk_union0 bu_t acc tmlist =
  case tmlist of
    [] => acc
  | (t::ts) => list_mk_union0 bu_t (list_mk_comb(bu_t, [acc,t])) ts

fun list_mk_union [] = raise ERR "list_mk_union" "term list empty"
  | list_mk_union (t::ts) =
      list_mk_union0 (Term.inst [alpha |-> base_type t] BAG_UNION_tm) t ts

fun strip_union0 acc t =
  if is_union t then let
    val (l,r) = dest_union t
  in
    strip_union0 (strip_union0 acc r) l
  end
  else t::acc

val strip_union = strip_union0 []

fun mk_insert (tm1, tm2) = let
  val bt = base_type tm2
  val bi = Term.inst [alpha |-> bt] BAG_INSERT_tm
in
  list_mk_comb(bi, [tm1, tm2])
end

val dest_insert = dest_binop "BAG_INSERT" "dest_insert"
val is_insert = can dest_insert

fun mk_all_distinct b = mk_icomb (BAG_ALL_DISTINCT_tm, b);
fun dest_all_distinct tm = let
  val (f, arg) = dest_comb tm
  val _ = (aconv f BAG_ALL_DISTINCT_tm) orelse 
          raise ERR "BAG_ALL_DISTINCT" ("not a BAG_ALL_DISTINCT")
in
  arg
end
val is_all_distinct = can dest_all_distinct


fun mk_card tm = 
  mk_icomb(BAG_CARD_tm, tm)
fun dest_card tm = let
  val (f, arg) = dest_comb tm
  val _ = (aconv f BAG_CARD_tm) orelse 
          raise ERR "BAG_CARD" ("not a BAG_CARD")
in
  arg
end
val is_card = can dest_card


fun mk_image (tm1, tm2) = 
  list_mk_icomb(BAG_IMAGE_tm, [tm1, tm2])
val dest_image = dest_binop "BAG_IMAGE" "dest_image"
val is_image = can dest_image

val is_empty = same_const EMPTY_BAG_tm

fun list_mk_insert (tms, t) =
  case tms of
    (h::_) => let
      val cnst = Term.inst [alpha |-> type_of h] BAG_INSERT_tm
    in
      List.foldr (fn (i,b) => list_mk_comb(cnst, [i,b])) t tms
    end
  | [] => t

fun strip_insert0 acc tm =
  if is_insert tm then let
    val (i,b) = dest_insert tm
  in
    strip_insert0 (i::acc) b
  end
  else (rev acc, tm)
val strip_insert = strip_insert0 []

fun mk_sub_bag (tm1, tm2) = let
  val bt = base_type tm1
  val sb = Term.inst [alpha |-> bt] SUB_BAG_tm
in
  list_mk_comb(sb, [tm1, tm2])
end
val dest_sub_bag = dest_binop "SUB_BAG" "dest_sub_bag"
val is_sub_bag = can dest_sub_bag

fun mk_bag (tms, ty) =
  list_mk_insert(tms, Term.inst [alpha |-> ty] EMPTY_BAG_tm)

fun dest_bag tm = let
  val (els, b) = strip_insert tm
  val _ = is_const b andalso fst (Term.dest_const b) = "EMPTY_BAG" orelse
    raise ERR "dest_bag" "Not a bag literal"
in
  (els, base_type b)
end

end
