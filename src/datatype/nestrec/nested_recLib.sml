(* =====================================================================*)
(* FILE          : nested_rec_def.sml                                   *)
(* DESCRIPTION   : the functor NestedRecTypeFunc applies DefTypeFunc    *)
(*                 and saves the resulting theorems away under the      *)
(*                 given names, and adds the appropriate bindings to    *)
(*                 sml.                                                 *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter                                          *)
(* DATE          : 94.03.13                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

structure nested_recLib :> nested_recLib =
struct

 type thm = Thm.thm

  val define_type = DefType.define_type;

end
