structure pred_setSimps :> pred_setSimps =
struct

  open HolKernel boolLib pred_setTheory

  val PRED_SET_ss = simpLib.merge_ss [pred_set_rwts, SET_SPEC_ss]

  val PRED_SET_AC_ss = simpLib.SSFRAG
    {name=SOME"PRED_SET_AC",
     convs = [], rewrs = [], filter = NONE, dprocs = [], congs = [],
     ac = [(UNION_ASSOC, UNION_COMM), (INTER_ASSOC, INTER_COMM)]
     }

end (* pred_setSimps *)
