(****************************************************************************)
(* FILE          : pair.sml                                                 *)
(* DESCRIPTION   : Decision procedure for pairs.                            *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 2nd June 1995                                            *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton, University of Edinburgh                     *)
(* DATE          : 28th January 1998                                        *)
(****************************************************************************)

structure DecidePair =
struct

local

open Term Dsyntax Psyntax DecisionSupport;

fun pair_discrim (_:bool) tm =
   if (is_var tm)
   then (fn _ => tm,[])
   else let val (f,args) = strip_comb tm
            fun reconstruct args' = list_mk_comb (f,args')
        in  if (is_const f) andalso
               (member (#Name (Rsyntax.dest_const f),length args)
                   [(",",2),("FST",1),("SND",1)])
            then (reconstruct,args)
            else raise Decide.failwith "pair_discrim"
        end;

in

val pair_proc =
   {Name = "pairs",
    Description = "Theory of equality on pairs",
    Author = "Richard J. Boulton",
    Discriminator = pair_discrim,
    Normalizer = DecisionConv.ALL_CONV,
    Procedure = Decide.make_incremental_procedure LazyRules.CONJ
                   CongruenceClosurePairs.PAIR_CONV};

end;

end; (* DecidePair *)
