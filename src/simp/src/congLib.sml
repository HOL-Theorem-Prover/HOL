structure congLib :> congLib =
congLibFn
  (struct
     (* Importing congLib still loads the modules it opened before
        congLibFn *)
     local open liteLib computeLib Trace Travrules Cond_rewr in end
     type reducer = Traverse.reducer
     type simpset = simpLib.simpset
     fun lift r = r
     val addctxt = Traverse.addctxt
     fun wrap_apply f (Traverse.REDUCER {name,initial,addcontext,apply}) =
       Traverse.REDUCER
         {name=name, initial=initial, addcontext=addcontext,
          apply=fn args as {relation=(_,refl),...} => f refl (apply args)}
     val CONGPROC = Opening.CONGPROC
     fun traversal ss =
       let val {rewriters,dprocs,travrules,...} = simpLib.traversedata_for_ss ss
       in
         ({rewriters=rewriters, dprocs=dprocs, travrules=travrules},
          Traverse.TRAVERSE)
       end
   end)
