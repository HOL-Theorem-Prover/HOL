structure finite_setSyntax :> finite_setSyntax =
struct

open HolKernel boolLib
open finite_setTheory

val ERR = mk_HOL_ERR "finite_setSyntax"


val s2 = HolKernel.syntax_fns2 "finite_set"

fun mk_fset_ty elty = mk_thy_type{Args = [elty], Thy = "finite_set", Tyop = "fset"}

val fset_ty = mk_fset_ty alpha
fun mk_empty ty = mk_thy_const{Name = "fEMPTY", Thy = "finite_set",
                               Ty = mk_fset_ty ty}

val empty_tm = mk_empty alpha

val (in_tm, mk_in, dest_in, is_in) = s2 "fIN"
val (insert_tm, mk_insert, dest_insert, is_insert) = s2 "fINSERT"
val (union_tm, mk_union, dest_union, is_union) = s2 "fUNION"
val (inter_tm, mk_inter, dest_inter, is_inter) = s2 "fINTER"

fun mk_set(l, ty) =
    List.foldr mk_insert (mk_empty ty) l
fun mk_set1 l =
    case l of
        [] => raise ERR "mk_set1" "Empty list"
      | h::_ => mk_set(l, type_of h)


end (* struct *)
