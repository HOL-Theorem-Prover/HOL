structure finite_mapSyntax :> finite_mapSyntax =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "finite_mapSyntax"

local open finite_mapTheory in end;

fun mk_fmap_ty (a, b) =
   mk_thy_type {Args = [a, b], Thy = "finite_map", Tyop = "fmap"}

fun is_fmap_ty ty =
   let
      val {Thy, Tyop, ...} = dest_thy_type ty
   in
      Thy = "finite_map" andalso Tyop = "fmap"
   end
   handle HOL_ERR _ => false

fun dest_fmap_ty ty =
   if is_fmap_ty ty
      then let
              val args = #2 (dest_type ty)
           in
              (hd args, hd (tl args))
           end
   else raise ERR "dest_fmap_ty" "Type not a finite map"

val sample_fmap_ty = mk_fmap_ty (alpha, beta)

fun finite_map_const name ty =
   mk_thy_const {Name = name, Thy = "finite_map", Ty = ty}

val fapply_t = finite_map_const "FAPPLY" (sample_fmap_ty --> alpha --> beta)
val fdom_t = finite_map_const "FDOM" (sample_fmap_ty --> alpha --> bool)
val fempty_t = finite_map_const "FEMPTY" sample_fmap_ty
val fevery_t = finite_map_const "FEVERY"
                            ((pairSyntax.mk_prod (alpha, beta) --> bool) -->
                             sample_fmap_ty --> bool)
val fupdate_t = finite_map_const "FUPDATE"
                            (sample_fmap_ty -->
                             pairSyntax.mk_prod (alpha, beta) -->
                             sample_fmap_ty)


fun mk_fempty(a,b) = Term.inst [alpha |-> a, beta |-> b] fempty_t
val is_fempty = same_const fempty_t

fun dest_fempty t =
    if is_fempty t
       then dest_fmap_ty (type_of t)
    else raise ERR "dest_fempty" "Term not an empty finite map"

fun dest_binop opn s fm =
   let
      val (f, args) = strip_comb fm
      val dest_name = "dest_" ^ s
      val _ = same_const f opn orelse
              raise ERR dest_name ("Term not an "^s)
      val _ = length args = 2 orelse
              raise ERR dest_name "Not applied to two arguments"
   in
      (hd args, hd (tl args))
   end

fun mk_binop opn s (fm, kvp) =
   let
      val (a_ty, b_ty) =
         dest_fmap_ty (type_of fm)
         handle HOL_ERR _ => raise ERR s "First argument not a finite map"
   in
      list_mk_comb (Term.inst [alpha |-> a_ty, beta |-> b_ty] opn, [fm, kvp])
   end

val mk_fupdate = mk_binop fupdate_t "mk_fupdate"
val dest_fupdate = dest_binop fupdate_t "fupdate"
val is_fupdate = can dest_fupdate

fun list_mk_fupdate (f,updl) =
   rev_itlist (fn p => fn map => mk_fupdate (map, p)) updl f

fun strip_fupdate tm =
   let
      fun strip acc t =
        case total dest_fupdate t of
           SOME (fmap, p) => strip (p :: acc) fmap
         | NONE => (t, acc)
   in
      strip [] tm
   end

val mk_fapply = mk_binop fapply_t "mk_fapply"
val dest_fapply = dest_binop fapply_t "fapply"
val is_fapply = can dest_fapply

fun mk_fdom t =
   let
      val (k_ty, v_ty) = dest_fmap_ty (type_of t)
   in
      mk_comb(Term.inst [alpha |-> k_ty, beta |-> v_ty] fdom_t, t)
   end

fun dest_fdom t =
   let
      val (f, x) = dest_comb t
   in
      if same_const f fdom_t
         then x
      else raise ERR "dest_fdom" "Operator of term not FDOM"
   end

val is_fdom = can dest_fdom

val is_fevery = same_const fevery_t
val dest_fevery = dest_binop fevery_t "fevery"
val is_fevery = can dest_fevery

val bop =
   HolKernel.syntax_fns "finite_map" 2 HolKernel.dest_binop HolKernel.mk_binop

val (flookup_t, mk_flookup, dest_flookup, is_flookup) = bop "FLOOKUP"

end
