structure progSyntax :> progSyntax =
struct

open Abbrev HolKernel progTheory

(* ----------------------------------------------------------------------- *)

val (cond_tm, mk_cond, dest_cond, is_cond) =
   HolKernel.syntax_fns "set_sep" 2 HolKernel.dest_monop HolKernel.mk_monop
      "cond"

val (star_tm, mk_star, dest_star, is_star) =
   HolKernel.syntax_fns "set_sep" 3 HolKernel.dest_binop
      (fn tm => fn (tm1, tm2) => boolSyntax.list_mk_icomb (tm, [tm1, tm2]))
      "STAR"

val list_mk_star = HolKernel.list_mk_lbinop (Lib.curry mk_star)
val strip_star = HolKernel.strip_binop (Lib.total dest_star)

val (spec_tm, mk_spec, dest_spec, is_spec) =
   HolKernel.syntax_fns "prog" 4 HolKernel.dest_quadop HolKernel.mk_quadop
      "SPEC"

(* ----------------------------------------------------------------------- *)

end
