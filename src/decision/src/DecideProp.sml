(****************************************************************************)
(* FILE          : prop.sml                                                 *)
(* DESCRIPTION   : Decision procedure for propositional formulas.           *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 24th March 1995                                          *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton, University of Edinburgh                     *)
(* DATE          : 28th January 1998                                        *)
(****************************************************************************)

structure DecideProp =
struct

local

open Type Term Dsyntax DecisionSupport;

val unops = ["~"]
and binops = ["/\\","\\/","==>"];

fun prop_discrim (_:bool) tm =
   let val (f,args) = strip_comb tm
   in  case (length args)
       of 0 => if ((is_var tm) andalso (type_of tm = bool)) orelse
                  (is_T tm) orelse (is_F tm)
               then (fn _ => tm,[])
               else Decide.failwith "prop_discrim"
        | 1 => if (is_const f) andalso
                  (member (#Name (Rsyntax.dest_const f)) unops)
               then (fn args' => list_mk_comb (f,args'),args)
               else Decide.failwith "prop_discrim"
        | 2 => if (is_const f) andalso
                  (member (#Name (Rsyntax.dest_const f)) binops)
               then (fn args' => list_mk_comb (f,args'),args)
               else Decide.failwith "prop_discrim"
        | _ => Decide.failwith "prop_discrim"
   end;

in

val prop_proc =
   {Name = "prop",
    Description = "Propositional tautologies",
    Author = "Richard J. Boulton",
    Discriminator = prop_discrim,
    Normalizer = DecisionConv.ALL_CONV,
    Procedure =
       Decide.make_incremental_procedure LazyRules.CONJ
          (LazyThm.mk_proved_pre_thm o Decide.NEGATE_CONV Taut.TAUT_CONV)};

end;

end; (* DecideProp *)
