structure bagLib :> bagLib = struct

open HolKernel Parse basicHol90Lib
open Psyntax simpLib boolSimps
infixr -->
infix |-> THENC

open bagTheory


fun ERR f s = HOL_ERR {origin_function = f, message = s,
                       origin_structure = "bagLib"};

(* remove x xs removes one instance of x from xs *)
fun remove x [] = raise ERR "remove" "no such element"
  | remove x (y::xs) = if x = y then xs else y::(remove x xs)

val num_ty = mk_type("num", [])
val bag_ty = Type.alpha --> num_ty

val BAG_INSERT_tm = mk_const("BAG_INSERT", alpha --> bag_ty --> bag_ty);
val BAG_UNION_tm = mk_const("BAG_UNION", bag_ty --> bag_ty --> bag_ty);
val BAG_DIFF_tm = mk_const("BAG_DIFF", bag_ty --> bag_ty --> bag_ty);
val EMPTY_BAG_tm = mk_const("EMPTY_BAG", bag_ty);
val SUB_BAG_tm = mk_const("SUB_BAG", bag_ty --> bag_ty --> bool);

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
  val _ = is_const b andalso #Name (Term.dest_const b) = "EMPTY_BAG" orelse
    raise ERR "dest_bag" "Not a bag literal"
in
  (els, base_type b)
end


val BAG_AC_ss = simpLib.SIMPSET {
    convs = [], rewrs = [], dprocs = [], congs = [],
    ac = [(SPEC_ALL ASSOC_BAG_UNION, SPEC_ALL COMM_BAG_UNION)],
    filter = NONE
};

fun remove_list [] l2 = l2
  | remove_list (x::xs) l2 = remove_list xs (remove x l2)

fun buac_prover ty = let
  fun type_inst ty = Rsyntax.INST_TYPE [alpha |-> ty]
in
  AC_CONV (type_inst ty ASSOC_BAG_UNION, type_inst ty COMM_BAG_UNION)
end

val SUB_BAG_UNION_eliminate' =
  hd (CONJUNCTS
      (CONV_RULE (SIMP_CONV bool_ss [FORALL_AND_THM])
       SUB_BAG_UNION_eliminate))
val BU_EMPTY_R = hd (CONJUNCTS BAG_UNION_EMPTY)

fun CANCEL_CONV tm = let
  val (mk_rel, thm, (arg1, arg2)) =
    (mk_sub_bag, SUB_BAG_UNION_eliminate', dest_sub_bag tm)
    handle HOL_ERR _ => (mk_eq, BAG_UNION_LEFT_CANCEL, dest_eq tm)
  val basetype = base_type arg1
  val bag_type = basetype --> num_ty
  val arg1_ts = strip_union arg1 and arg2_ts = strip_union arg2
  fun common [] _ = []  (* like intersect but no setifying *)
    | common _ [] = []
    | common (x::xs) y = x::common xs (remove x y)
    handle _ => common xs y
  val common_part = common arg1_ts arg2_ts
  val _ = not (null common_part) orelse
    raise ERR "CANCEL_CONV" "No common parts to eliminate"
  val rem1 = remove_list common_part arg1_ts
  val rem2 = remove_list common_part arg2_ts
  val cpt = list_mk_union common_part
  val ac1 = mk_eq(arg1, if null rem1 then cpt
                        else mk_union (cpt, list_mk_union rem1))
  val ac2 = mk_eq(arg2, if null rem2 then cpt
                        else mk_union (cpt, list_mk_union rem2))
  val ac1thm = EQT_ELIM (buac_prover basetype ac1)
  val ac2thm = EQT_ELIM (buac_prover basetype ac2)
  fun add_emptybag thm = let
    val r = rhs (concl thm)
  in
    TRANS thm
    (SYM (REWR_CONV BU_EMPTY_R (mk_union(cpt, mk_bag([], basetype)))))
  end
  val thm1 = if null rem1 then add_emptybag ac1thm else ac1thm
  val thm2 = if null rem2 then add_emptybag ac2thm else ac2thm
  val v1 = genvar bag_type and v2 = genvar bag_type
  val template = mk_rel (v1, v2)
in
  Rsyntax.SUBST_CONV [v1 |-> thm1, v2 |-> thm2] template THENC
  REWR_CONV thm
end tm

val BAG_ss = rewrites [BAG_UNION_EMPTY, BAG_DIFF_EMPTY, SUB_BAG_REFL,
                       SUB_BAG_EMPTY]


end;
