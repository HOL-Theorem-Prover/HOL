(* ===================================================================== *)
(* FILE          : barendregt.sig                                        *)
(* VERSION       : 1.0                                                   *)
(* DESCRIPTION   : Tactic to reduce proper substitution to the much      *)
(*                 simpler operation of naive substitution.              *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : October 24, 2000                                      *)
(* COPYRIGHT     : Copyright (c) 2000 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)

signature barendregt =
sig

type tactic  = Abbrev.tactic



val SHIFT_LAMBDAS_TAC : tactic


val MAKE_SIMPLE_SUBST_TAC : tactic

val SIMPLE_SUBST_TAC : tactic

end
