structure tripleSyntax :> tripleSyntax =
struct

open Abbrev HolKernel
open tripleTheory

(* ----------------------------------------------------------------------- *)

val (triple_tm, mk_triple, dest_triple, is_triple) =
   HolKernel.syntax_fns "triple" 4 HolKernel.dest_quadop HolKernel.mk_quadop
      "TRIPLE"

val (case_sum_tm, mk_case_sum, dest_case_sum, is_case_sum) =
   HolKernel.syntax_fns "triple" 3
      HolKernel.dest_triop HolKernel.mk_triop "case_sum"

fun dest_model tm = let val (m, _, _, _) = dest_triple tm in m end
fun dest_pre tm = let val (_, p, _, _) = dest_triple tm in p end
fun dest_code tm = let val (_, _, c, _) = dest_triple tm in c end
fun dest_post tm = let val (_, _, _, q) = dest_triple tm in q end
fun dest_pre_post tm = let val (_, p, _, q) = dest_triple tm in (p, q) end

(* ----------------------------------------------------------------------- *)

end
