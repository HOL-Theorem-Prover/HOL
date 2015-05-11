structure temporalSyntax :> temporalSyntax =
struct

open Abbrev HolKernel progSyntax temporalTheory

val ERR = Feedback.mk_HOL_ERR "tripleSyntax"

(* ----------------------------------------------------------------------- *)

fun syntax_fns n d m =
   HolKernel.syntax_fns {n = n, dest = d, make = m} "temporal"

val s1 = syntax_fns 3 HolKernel.dest_monop HolKernel.mk_monop
val s2 = syntax_fns 4 HolKernel.dest_binop HolKernel.mk_binop

val (temporal_tm, mk_temporal, dest_temporal, is_temporal) =
   HolKernel.syntax_fns3 "temporal" "TEMPORAL"
val (now_tm, mk_now, dest_now, is_now) = s1 "NOW"
val (next_tm, mk_next, dest_next, is_next) = s1 "NEXT"
val (eventually_tm, mk_eventually, dest_eventually, is_eventually) =
   s1 "EVENTUALLY"
val (always_tm, mk_always, dest_always, is_always) = s1 "ALWAYS"
val (t_and_tm, mk_t_and, dest_t_and, is_t_and) = s2 "T_AND"
val (t_implies_tm, mk_t_implies, dest_t_implies, is_t_implies) = s2 "T_IMPLIES"

(* ----------------------------------------------------------------------- *)

end
