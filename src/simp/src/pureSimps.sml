structure pureSimps :> pureSimps =
struct

  open simpLib Cond_rewr

  val PURE_ss = SIMPSET
    {convs = [],
     rewrs = [],
     congs = [],
     filter = SOME mk_cond_rewrs,
     ac = [],
     dprocs = []}

  val pure_ss = mk_simpset [PURE_ss]


end