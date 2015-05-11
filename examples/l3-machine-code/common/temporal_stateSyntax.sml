structure temporal_stateSyntax :> temporal_stateSyntax =
struct

open Abbrev HolKernel progSyntax temporal_stateTheory

(* ----------------------------------------------------------------------- *)

val (temporal_next_tm, mk_temporal_next, dest_temporal_next, is_temporal_next) =
   HolKernel.syntax_fns4 "temporal_state" "TEMPORAL_NEXT"

fun dest_pre tm = let val (_, p, _, _) = dest_temporal_next tm in p end
fun dest_code tm = let val (_, _, c, _) = dest_temporal_next tm in c end
fun dest_post tm = let val (_, _, _, q) = dest_temporal_next tm in q end
fun dest_pre_post tm =
   let val (_, p, _, q) = dest_temporal_next tm in (p, q) end

fun dest_spec' tm =
   progSyntax.dest_spec tm handle HOL_ERR _ => dest_temporal_next tm
fun dest_pre' tm = progSyntax.dest_pre tm handle HOL_ERR _ => dest_pre tm
fun dest_code' tm = progSyntax.dest_code tm handle HOL_ERR _ => dest_code tm
fun dest_post' tm = progSyntax.dest_post tm handle HOL_ERR _ => dest_post tm
fun dest_pre_post' tm =
   progSyntax.dest_pre_post tm handle HOL_ERR _ => dest_pre_post tm

fun mk_spec_or_temporal_next model_tm =
   let
       val tm1 = boolSyntax.mk_icomb (progSyntax.spec_tm, model_tm)
       val tm2 = boolSyntax.mk_icomb (temporal_next_tm, model_tm)
   in
      fn b =>
         let
            val mk = HolKernel.list_mk_icomb (if b then tm2 else tm1)
         in
            fn (p, c, q) => mk [p, c, q]
         end
   end

(* ----------------------------------------------------------------------- *)

end
