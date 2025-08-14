structure bagSyntax :> bagSyntax =
struct

open HolKernel Parse boolLib simpLib boolSimps bagTheory;

val ERR = mk_HOL_ERR "bagLib";

val num_ty = numSyntax.num

val bag_ty = Type.alpha --> num_ty
fun is_bag_ty ty = #2 (dom_rng ty) = num_ty handle HOL_ERR _ => false

val (BAG_INSERT_tm, mk_insert, dest_insert, is_insert) =
    syntax_fns2 "bag" "BAG_INSERT"
val (BAG_UNION_tm, mk_union, dest_union, is_union) =
    syntax_fns2 "bag" "BAG_UNION"
val (BAG_DIFF_tm, mk_diff, dest_diff, is_diff) =
    syntax_fns2 "bag" "BAG_DIFF"
val (BAG_CARD_tm, mk_card, dest_card, is_card) =
    syntax_fns1 "bag" "BAG_CARD"
val (BAG_EVERY_tm, mk_every, dest_every, is_every) =
    syntax_fns2 "bag" "BAG_EVERY"
val (BAG_ALL_DISTINCT_tm, mk_all_distinct, dest_all_distinct, is_all_distinct) =
    syntax_fns1 "bag" "BAG_ALL_DISTINCT"
val (SUB_BAG_tm, mk_sub_bag, dest_sub_bag, is_sub_bag) =
    syntax_fns2 "bag" "SUB_BAG"
val (BAG_IMAGE_tm, mk_image, dest_image, is_image) =
    syntax_fns2 "bag" "BAG_IMAGE"

val EMPTY_BAG_tm = mk_const("EMPTY_BAG", bag_ty);
val is_empty = same_const EMPTY_BAG_tm

val BAG_EQ_tm =
    mk_thy_const{Thy="min", Name = "=", Ty = bag_ty --> bag_ty --> bool};

fun base_type tm = let
  val ty = type_of tm
  val (dom,rng) = dom_rng ty
in
  if rng = num_ty then dom
  else raise ERR "bag_base_type" "term not a bag"
end

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
