structure pred_setSimps :> pred_setSimps =
struct

  open HolKernel boolLib pred_setTheory
  val (Type,Term) = Parse.parse_from_grammars pred_setTheory.pred_set_grammars

  val simpLib.SIMPSET {rewrs = ps_rwts, ...} = pred_setTheory.pred_set_rwts

  val SET_SPEC_CONV =
      {conv = K (K (PGspec.SET_SPEC_CONV pred_setTheory.GSPECIFICATION)),
       key = SOME ([], ``(x:'a) IN GSPEC (f:'b -> 'a # bool)``),
       name = "SET_SPEC_CONV",
       trace = 2}

  val SET_SPEC_ss = simpLib.SIMPSET { ac = [], congs = [],
                                      convs = [SET_SPEC_CONV], dprocs = [],
                                      filter = NONE, rewrs = []}

  val PRED_SET_ss = simpLib.SIMPSET { ac = [], congs = [],
                                      convs = [SET_SPEC_CONV], dprocs = [],
                                      filter = NONE, rewrs = ps_rwts }

  val PRED_SET_AC_ss = simpLib.SIMPSET
    {
     convs = [], rewrs = [], filter = NONE, dprocs = [], congs = [],
     ac = [(UNION_ASSOC, UNION_COMM), (INTER_ASSOC, INTER_COMM)]
     }

  (* the rewrites in PRED_SET_ss are already in srw_ss because they are
     "exported" by pred_setScript. *)

  val _ = BasicProvers.augment_srw_ss [SET_SPEC_ss];

end (* pred_setSimps *)
