(* congLibFn over the extended traversal: simpset reducers keep their
   configured callbacks and congruences are constructed threaded. *)
structure congExtLib :> congExtLib =
struct

open HolKernel boolLib

structure Generic =
congLibFn
  (struct
     type reducer = TraverseExt.reducer
     type simpset = simpExtLib.simpset
     val lift = TraverseExt.lift
     val addctxt = TraverseExt.addctxt
     fun eq_reducer_wrapper reducer =
       let
         val {name,initial,addcontext,apply} =
             TraverseExt.reducer_config_data reducer
         fun wrapped (args as {relation=(_,refl),...}) tm =
           let
             val eqthm = apply args tm
             val relthm = refl tm
           in
             CONV_RULE (RAND_CONV (REWR_CONV eqthm)) relthm
           end
       in
         TraverseExt.CONFIG_REDUCER
           {name=name, addcontext=addcontext, apply=wrapped, initial=initial}
       end
     val CONGPROC = Opening.THREADED_CONGPROC
     (* Match SIMP_QCONV: only conversion-consumed settings opt into
        per-application context refresh. *)
     fun traversal ss =
       let
         val config = simpExtLib.traverseconfig_for_ss ss
         val ({rewriters,dprocs,travrules,...},traverse) =
           case config of
               {subgoaler=NONE,solvers=[],cond_depth=NONE,term_ord=NONE} =>
                 (simpExtLib.traversedata_for_ss ss, TraverseExt.TRAVERSE)
             | _ =>
                 (#1 (simpExtLib.xtraversedata_for_ss ss),
                  fn data => TraverseExt.XTRAVERSE (data,config))
       in
         ({rewriters=rewriters, dprocs=dprocs, travrules=travrules}, traverse)
       end
   end)
open Generic

(* Public fragments can be lifted without running collectors/factories.
   Opaque compiled congsets cannot be promoted. *)
fun lift_fragment (congLib.CSFRAG {rewrs,relations,dprocs,congs}) =
  CSFRAG {rewrs=rewrs, relations=relations,
          dprocs=map TraverseExt.lift dprocs, congs=congs};

end
