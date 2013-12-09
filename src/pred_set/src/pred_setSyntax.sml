structure pred_setSyntax :> pred_setSyntax =
struct

local open pred_setTheory in end;

open HolKernel Abbrev;

val ERR = mk_HOL_ERR "pred_setSyntax"

(*---------------------------------------------------------------------------*)
(* Types                                                                     *)
(*---------------------------------------------------------------------------*)

fun mk_set_type ty = ty --> bool

fun dest_set_type ty =
   case total dom_rng ty of
      SOME (ty1, ty2) =>
         if ty2 = Type.bool
            then ty1
         else raise ERR "dest_set_type" "not an instance of 'a -> bool"
    | NONE => raise ERR "dest_set_type" "not an instance of 'a -> bool"

val is_set_type  = Lib.can dest_set_type

(*---------------------------------------------------------------------------*)
(* Get the type of the elements of a set                                     *)
(*---------------------------------------------------------------------------*)

fun eltype tm = dest_set_type (type_of tm)

(*---------------------------------------------------------------------------*)
(* Set constants. Note that "IN" is alredy defined in boolTheory.            *)
(*---------------------------------------------------------------------------*)

fun syntax_fns n d m = HolKernel.syntax_fns "pred_set" n d m
val t1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop
val t2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop
val s1 = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop
val s2 = syntax_fns 3 HolKernel.dest_binop HolKernel.mk_binop
val t3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop

val (in_tm, mk_in, dest_in, is_in) =
   HolKernel.syntax_fns "bool" 2 HolKernel.dest_binop HolKernel.mk_binop "IN"

val (insert_tm, mk_insert, dest_insert, is_insert) = s2 "INSERT"
val (inter_tm, mk_inter, dest_inter, is_inter) = s2 "INTER"
val (union_tm, mk_union, dest_union, is_union) = s2 "UNION"
val (diff_tm, mk_diff, dest_diff, is_diff) = s2 "DIFF"
val (delete_tm, mk_delete, dest_delete, is_delete) = s2 "DELETE"
val (gspec_tm, mk_gspec, dest_gspec, is_gspec) = s1 "GSPEC"
val (compl_tm, mk_compl, dest_compl, is_compl) = s1 "COMPL"
val (card_tm, mk_card, dest_card, is_card) = t1 "CARD"
val (image_tm, mk_image, dest_image, is_image) = s2 "IMAGE"
val (finite_tm, mk_finite, dest_finite, is_finite) = t1 "FINITE"
val (sing_tm, mk_sing, dest_sing, is_sing) = t1 "SING"
val (subset_tm, mk_subset, dest_subset, is_subset) = t2 "SUBSET"
val (psubset_tm, mk_psubset, dest_psubset, is_psubset) = t2 "PSUBSET"
val (pow_tm, mk_pow, dest_pow, is_pow) = s1 "POW"
val (disjoint_tm, mk_disjoint, dest_disjoint, is_disjoint) = t2 "DISJOINT"
val (bigunion_tm, mk_bigunion, dest_bigunion, is_bigunion) = s1 "BIGUNION"
val (biginter_tm, mk_biginter, dest_biginter, is_biginter) = s1 "BIGINTER"
val (cross_tm, mk_cross, dest_cross, is_cross) = s2 "CROSS"
val (count_tm, mk_count, dest_count, is_count) = s1 "count"
val (max_set_tm, mk_max_set, dest_max_set, is_max_set) = t1 "MAX_SET"
val (min_set_tm, mk_min_set, dest_min_set, is_min_set) = t1 "MIN_SET"
val (sum_image_tm, mk_sum_image, dest_sum_image, is_sum_image) = t2 "SUM_IMAGE"
val (sum_set_tm, mk_sum_set, dest_sum_set, is_sum_set) = t1 "SUM_SET"
val (choice_tm, mk_choice, dest_choice, is_choice) = t1 "CHOICE"
val (rest_tm, mk_rest, dest_rest, is_rest) = s1 "REST"
val (inj_tm, mk_inj, dest_inj, is_inj) = t3 "INJ"
val (surj_tm, mk_surj, dest_surj, is_surj) = t3 "SURJ"
val (bij_tm, mk_bij, dest_bij, is_bij) = t3 "BIJ"
val (linv_tm, mk_linv, dest_linv, is_linv) = t3 "LINV"
val (rinv_tm, mk_rinv, dest_rinv, is_rinv) = t3 "RINV"

(*---------------------------------------------------------------------------*)
(* Empty set                                                                 *)
(*---------------------------------------------------------------------------*)

val empty_tm = prim_mk_const {Name = "EMPTY", Thy = "pred_set"}

fun mk_empty ty =
   inst [alpha |-> ty] empty_tm
   handle HOL_ERR _ => raise ERR "mk_empty" ""

fun dest_empty tm =
   if same_const tm empty_tm
      then type_of tm
   else raise ERR "dest_empty" "not the empty set"

val is_empty = Lib.can dest_empty

(*---------------------------------------------------------------------------*)
(* Unversal set                                                              *)
(*---------------------------------------------------------------------------*)

val univ_tm = prim_mk_const {Name = "UNIV", Thy = "pred_set"}

fun mk_univ ty =
   inst [alpha |-> ty] univ_tm
   handle HOL_ERR _ => raise ERR "mk_univ" ""

fun dest_univ tm =
   if same_const tm univ_tm
      then type_of tm
   else raise ERR "dest_univ" "not the universal set"

val is_univ = Lib.can dest_univ

(*---------------------------------------------------------------------------*)
(* Infiniteness                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_infinite tm =
   boolSyntax.mk_neg (mk_finite tm)
   handle HOL_ERR _ => raise ERR "mk_infinite" "not a set?"

fun dest_infinite t =
   let
      val t' = boolSyntax.dest_neg t
   in
      dest_finite t'
   end
   handle HOL_ERR _ =>
          raise ERR "dest_infinite" "not an application of INFINITE"

val is_infinite = Lib.can dest_infinite

(*---------------------------------------------------------------------------*)
(* Finitely iterated insertion                                               *)
(*---------------------------------------------------------------------------*)

fun prim_mk_set (l, ty) =
   itlist (curry mk_insert) l (mk_empty ty)
   handle HOL_ERR _ => raise ERR "prim_mk_set" ""

fun mk_set [] = raise ERR "mk_set" "empty set"
  | mk_set (els as (h::_)) =
      itlist (curry mk_insert) els (mk_empty (type_of h))
      handle HOL_ERR _ => raise ERR "mk_set" ""

val strip_set =
   let
      fun strip tm =
         let
            val (h, t) = dest_insert tm
         in
            h::strip t
         end
         handle HOL_ERR _ =>
                if same_const tm empty_tm
                   then []
                else raise ERR "strip_set" "not an enumerated set"
   in
      strip
   end

(*---------------------------------------------------------------------------*)
(* Set comprehensions                                                        *)
(*---------------------------------------------------------------------------*)

fun prim_mk_set_spec (tm1, tm2, sharedvars) =
   let
      val tuple = pairSyntax.list_mk_pair sharedvars
   in
      mk_comb (inst [alpha |-> type_of tm1, beta |-> type_of tuple] gspec_tm,
               pairSyntax.mk_pabs (tuple, pairSyntax.mk_pair (tm1, tm2)))
   end
   handle HOL_ERR _ => raise ERR "prim_mk_set_spec" ""

fun mk_set_spec (tm1, tm2) =
   let
      val shared = intersect (free_vars_lr tm1) (free_vars_lr tm2)
   in
      prim_mk_set_spec (tm1, tm2, shared)
   end
   handle e as HOL_ERR _ => raise wrap_exn "mk_set_spec" "" e

fun dest_set_spec tm =
   case total dest_comb tm of
      SOME (c, M) =>
         if same_const c gspec_tm
            then pairSyntax.dest_pair (snd (pairSyntax.dest_pabs M))
         else raise ERR "dest_set_spec" "not a set comprehension"
    | NONE => raise ERR "dest_set_spec" "not a set comprehension"

val is_set_spec = Lib.can dest_set_spec

(*---------------------------------------------------------------------------*)
(* Big union                                                                 *)
(*---------------------------------------------------------------------------*)

fun list_mk_bigunion sets = mk_bigunion (mk_set sets)
fun strip_bigunion tm = strip_set (dest_bigunion tm)

(*---------------------------------------------------------------------------*)
(* Big intersection                                                          *)
(*---------------------------------------------------------------------------*)

fun list_mk_biginter sets = mk_biginter (mk_set sets)
fun strip_biginter tm = strip_set (dest_biginter tm)

end
