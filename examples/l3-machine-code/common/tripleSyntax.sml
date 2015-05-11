structure tripleSyntax :> tripleSyntax =
struct

open Abbrev HolKernel
open tripleTheory

(* ----------------------------------------------------------------------- *)

val (triple_tm, mk_triple, dest_triple, is_triple) =
   HolKernel.syntax_fns4 "triple" "TRIPLE"

val (case_sum_tm, mk_case_sum, dest_case_sum, is_case_sum) =
   HolKernel.syntax_fns3 "triple" "case_sum"

fun dest_model tm = let val (m, _, _, _) = dest_triple tm in m end
fun dest_pre tm = let val (_, p, _, _) = dest_triple tm in p end
fun dest_code tm = let val (_, _, c, _) = dest_triple tm in c end
fun dest_post tm = let val (_, _, _, q) = dest_triple tm in q end
fun dest_pre_post tm = let val (_, p, _, q) = dest_triple tm in (p, q) end

fun get_component P thm =
   case Thm.hyp thm of
      [h] => let
                val (l, r) = boolSyntax.dest_eq h
                val l = pairSyntax.strip_pair l
                val r = pairSyntax.strip_pair r
             in
                case Lib.total (Lib.index P) r of
                   SOME n => List.nth (l, n)
                 | NONE => raise ERR "get_component" "not found"
             end
    | _ => raise ERR "get_component" "not single hyp"

(* ----------------------------------------------------------------------- *)

end
