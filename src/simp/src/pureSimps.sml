structure pureSimps :> pureSimps =
struct

open simpLib;

val PURE_ss = SSFRAG
    {name = SOME "PURE",
     convs  = [],
     rewrs  = [],
     congs  = [],
     ac     = [],
     filter = SOME Cond_rewr.mk_cond_rewrs,
     dprocs = []}

val pure_ss = mk_simpset [PURE_ss]

end
