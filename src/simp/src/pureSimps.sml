structure pureSimps :> pureSimps =
struct

  open simpLib 

  val PURE_ss = SIMPSET
    {convs = [],
     rewrs = [],
     congs = [],
     filter = SOME Cond_rewr.mk_cond_rewrs,
     ac = [],
     dprocs = []}

  val pure_ss = mk_simpset [PURE_ss]


end
