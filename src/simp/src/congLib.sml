structure congLib :> congLib =
congLibFn
  (struct
     (* Importing congLib still loads the modules it opened before
        congLibFn *)
     local open liteLib computeLib Trace Travrules Cond_rewr in end
     open HolKernel boolLib
     type reducer = Traverse.reducer
     type simpset = simpLib.simpset
     fun lift r = r
     val addctxt = Traverse.addctxt
     fun eq_reducer_wrapper (Traverse.REDUCER data) = let
       val name = #name data
       val initial = #initial data
       val addcontext = #addcontext data

       fun apply {solver,conv,context,stack,relation as (_, refl)} tm = let
         val eqthm = #apply data
                            {solver=solver,conv=conv,
                             context=context,stack=stack,
                             relation=relation}
                            tm
         val congThm = refl tm
         val congThm = CONV_RULE (RAND_CONV (REWR_CONV eqthm)) congThm
       in
         congThm
       end
     in
       Traverse.REDUCER {name=name,addcontext=addcontext, apply=apply,
                         initial=initial}
     end
     val CONGPROC = Opening.CONGPROC
     fun traversal ss =
       let val {rewriters,dprocs,travrules,...} = simpLib.traversedata_for_ss ss
       in
         ({rewriters=rewriters, dprocs=dprocs, travrules=travrules},
          Traverse.TRAVERSE)
       end
   end)
