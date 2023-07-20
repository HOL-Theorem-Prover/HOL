structure finite_mapSyntax :> finite_mapSyntax =
struct

open HolKernel boolLib

val ERR = Feedback.mk_HOL_ERR "finite_mapSyntax"

local open finite_mapTheory in end;

fun mk_fmap_ty (a, b) =
   Type.mk_thy_type {Thy = "finite_map", Tyop = "fmap", Args = [a, b]}

fun dest_fmap_ty ty =
  case Lib.total Type.dest_thy_type ty of
    SOME {Thy = "finite_map", Tyop = "fmap", Args = [a, b]} => (a, b)
  | _ => raise ERR "dest_fmap_ty" "Type not a finite map"

val is_fmap_ty = Lib.can dest_fmap_ty

val fempty_tm = Term.prim_mk_const {Name = "FEMPTY", Thy = "finite_map"}
fun mk_fempty (a, b) = Term.inst [Type.alpha |-> a, Type.beta |-> b] fempty_tm
val is_fempty = Term.same_const fempty_tm

fun dest_fempty t =
    if is_fempty t
       then dest_fmap_ty (type_of t)
    else raise ERR "dest_fempty" "Term not an empty finite map"

val s1 = HolKernel.syntax_fns
           {n = 2, dest = HolKernel.dest_monop, make = HolKernel.mk_monop}
           "finite_map"

val (fdom_tm, mk_fdom, dest_fdom, is_fdom) = s1 "FDOM"
val (frange_tm, mk_frange, dest_frange, is_frange) = s1 "FRANGE"

val (fcard_tm, mk_fcard, dest_fcard, is_fcard) =
   HolKernel.syntax_fns1 "finite_map" "FCARD"

val (fapply_tm, mk_fapply, dest_fapply, is_fapply) =
   HolKernel.syntax_fns2 "finite_map" "FAPPLY"

val (drestrict_tm, mk_drestrict, dest_drestrict, is_drestrict) =
   HolKernel.syntax_fns2 "finite_map" "DRESTRICT"

val (fdiff_tm, mk_fdiff, dest_fdiff, is_fdiff) =
   HolKernel.syntax_fns2 "finite_map" "FDIFF"

val (fevery_tm, mk_fevery, dest_fevery, is_fevery) =
   HolKernel.syntax_fns2 "finite_map" "FEVERY"

val (flookup_tm, mk_flookup, dest_flookup, is_flookup) =
   HolKernel.syntax_fns2 "finite_map" "FLOOKUP"

val (funion_tm, mk_funion, dest_funion, is_funion) =
   HolKernel.syntax_fns2 "finite_map" "FUNION"

val (fmap_map2_tm, mk_fmap_map2, dest_fmap_map2, is_fmap_map2) =
   HolKernel.syntax_fns2 "finite_map" "FMAP_MAP2"

val (fun_fmap_tm, mk_fun_fmap, dest_fun_fmap, is_fun_fmap) =
   HolKernel.syntax_fns2 "finite_map" "FUN_FMAP"

val (fupdate_tm, mk_fupdate, dest_fupdate, is_fupdate) =
   HolKernel.syntax_fns2 "finite_map" "FUPDATE"

val (fupdate_list_tm, mk_fupdate_list, dest_fupdate_list, is_fupdate_list) =
   HolKernel.syntax_fns2 "finite_map" "FUPDATE_LIST"

val (rrestrict_tm, mk_rrestrict, dest_rrestrict, is_rrestrict) =
   HolKernel.syntax_fns2 "finite_map" "RRESTRICT"

val (fmerge_tm, mk_fmerge, dest_fmerge, is_fmerge) =
   HolKernel.syntax_fns3 "finite_map" "FMERGE"

fun list_mk_fupdate (f,updl) =
   Lib.rev_itlist (fn p => fn map => mk_fupdate (map, p)) updl f

val strip_fupdate =
   let
      fun strip acc t =
        case Lib.total dest_fupdate t of
           SOME (fmap, p) => strip (p :: acc) fmap
         | NONE => (t, acc)
   in
      strip []
   end

end
