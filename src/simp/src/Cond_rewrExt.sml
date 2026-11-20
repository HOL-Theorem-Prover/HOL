(* Bounded-control binding for the paired runners of
   Cond_rewr.COND_REWR_CONVS. *)
structure Cond_rewrExt :> Cond_rewrExt =
struct
open HolKernel boolLib liteLib Trace

(* Preserve the observable diagnostic origin of the conditional engine. *)
fun WRAP_ERR x = STRUCT_WRAP "Cond_rewr" x
fun ERR x = STRUCT_ERR "Cond_rewr" x

type config = Cond_rewr.config
type runners = Cond_rewr.runners
val is_var_perm = Cond_rewr.is_var_perm
val COND_REWR_CONVS = Cond_rewr.COND_REWR_CONVS

   fun COND_REWR_CONV_WITH_CONFIG nmth bounded =
      #configured (COND_REWR_CONVS nmth bounded);

   fun COND_REWR_CONV_WITH_CONTEXT nmth bounded =
      let val conv = COND_REWR_CONV_WITH_CONFIG nmth bounded
      in
        fn {solver,stack,cond_depth,term_ord} =>
           conv {solver=solver, stack=stack, cond_depth=SOME cond_depth,
                 term_ord=term_ord}
      end;

(* Binding happens at tracked construction, not at projection. No shadow
   allowance: aliases/conjuncts may deliberately supply the same reference.
   As in the baseline bound wrapper, failures do not spend an allowance. *)
datatype prepared = Prepared of
  {shape : runners, bounded : bool, bound : runners}
fun is_bounded BoundedRewrites.UNBOUNDED = false
  | is_bounded (BoundedRewrites.BOUNDED _) = true
fun bind (shape : runners) control =
  case control of
      BoundedRewrites.UNBOUNDED => shape
    | BoundedRewrites.BOUNDED r =>
        {legacy = fn solver => fn stack => fn tm =>
           if !r = 0 then failwith "exceeded rewrite bound"
           else #legacy shape solver stack tm before Portable.dec r,
         configured = fn ctxt => fn tm =>
           if !r = 0 then failwith "exceeded rewrite bound"
           else #configured shape ctxt tm before Portable.dec r}
fun prepare nmth control =
  let
    val bounded = is_bounded control
    val shape = COND_REWR_CONVS nmth bounded
  in Prepared {shape=shape,bounded=bounded,bound=bind shape control} end

(* Replay can bind a new actual control to an already prepared matcher.
   Bounded status affects permutation checking inside that matcher, so it
   cannot be changed by rebinding. No preparation or tracing happens here. *)
fun rebind (Prepared {shape,bounded,...}) control =
  if bounded = is_bounded control then
    Prepared {shape=shape,bounded=bounded,bound=bind shape control}
  else raise ERR ("rebind","cannot change prepared bounded status")
fun runners (Prepared {bound,...}) = bound
end
