(****************************************************************************)
(* FILE          : uninterp.sml                                             *)
(* DESCRIPTION   : Decision procedure for uninterpreted function symbols.   *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 22nd February 1995                                       *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton, University of Edinburgh                     *)
(* DATE          : 28th January 1998                                        *)
(****************************************************************************)

structure DecideUninterp =
struct

local  open Term Dsyntax

fun uninterp_discrim unknown tm =
   let val (f,args) = strip_comb tm
   in  if (is_var f) orelse (unknown andalso (is_const f))
       then (fn args' => list_mk_comb (f,args'),args)
       else Decide.failwith "uninterp_discrim"
   end;

in

val uninterp_proc =
   {Name = "uninterp",
    Description = "Theory of equality on uninterpreted function symbols",
    Author = "Richard J. Boulton",
    Discriminator = uninterp_discrim,
    Normalizer = DecisionConv.ALL_CONV,
    Procedure = Decide.make_incremental_procedure LazyRules.CONJ
                   CongruenceClosure.CONGRUENCE_CONV};

end;

end; (* DecideUninterp *)
