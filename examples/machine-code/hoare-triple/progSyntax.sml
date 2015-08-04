structure progSyntax :> progSyntax =
struct

open Abbrev HolKernel progTheory

(* ----------------------------------------------------------------------- *)

fun syntax_fns n d m =
   HolKernel.syntax_fns {n = n, dest = d, make = m} "set_sep"

val (cond_tm, mk_cond, dest_cond, is_cond) =
   syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop "cond"

val (star_tm, mk_star, dest_star, is_star) =
   syntax_fns 3 HolKernel.dest_binop
      (fn tm => fn (tm1, tm2) => boolSyntax.list_mk_icomb (tm, [tm1, tm2]))
      "STAR"

val list_mk_star = HolKernel.list_mk_lbinop (Lib.curry mk_star)
val strip_star = HolKernel.strip_binop (Lib.total dest_star)

val (spec_tm, mk_spec, dest_spec, is_spec) =
   HolKernel.syntax_fns4 "prog" "SPEC"

fun dest_pre tm = let val (_, p, _, _) = dest_spec tm in p end
fun dest_code tm = let val (_, _, c, _) = dest_spec tm in c end
fun dest_post tm = let val (_, _, _, q) = dest_spec tm in q end
fun dest_pre_post tm = let val (_, p, _, q) = dest_spec tm in (p, q) end

(* ----------------------------------------------------------------------- *)

end
