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
     fun wrap_apply f reducer =
       let
         val {name,initial,addcontext,apply} =
             TraverseExt.reducer_config_data reducer
       in
         TraverseExt.CONFIG_REDUCER
           {name=name, initial=initial, addcontext=addcontext,
            apply=fn args as {relation=(_,refl),...} => f refl (apply args)}
       end
     val CONGPROC = Opening.THREADED_CONGPROC
     fun traversal ss =
       let
         val ({rewriters,dprocs,travrules,...},traverse) =
             simpExtLib.traversal_for_ss ss
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
