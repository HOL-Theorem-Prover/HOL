structure pureSimps :> pureSimps =
struct

open Lib Drule simpLib 

val std_rewr_maker = Cond_rewr.mk_cond_rewrs;

(*---------------------------------------------------------------------------*)
(* Wrap the standard rewrite maker with some guff that attaches a            *)
(* BOUNDED/UNBOUNDED tag to the resulting rewrites.                          *)
(*---------------------------------------------------------------------------*)

fun bound_filter th =
  case total DEST_BOUNDED th
     of NONE => map MK_UNBOUNDED (std_rewr_maker th)
      | SOME (th',n) => map (C MK_BOUNDED n) (std_rewr_maker th')

val PURE_ss = SIMPSET
    {convs  = [],
     rewrs  = [],
     congs  = [],
     ac     = [],
     filter = SOME bound_filter,
     dprocs = []}

val pure_ss = mk_simpset [PURE_ss]

end
