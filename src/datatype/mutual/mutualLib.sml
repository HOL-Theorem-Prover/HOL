(* ===================================================================== *)
(* FILE          : mutualLib.sml                                         *)
(* VERSION       : 1.0                                                   *)
(* DESCRIPTION   : Creates the structure of the exported identifiers     *)
(*                 for the improved mutual recursion library.            *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : April 21, 1998                                        *)
(* COPYRIGHT     : Copyright (c) 1998 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)


structure mutualLib :> mutualLib =
struct

 type 'a quotation = 'a frag list
 type hol_type = Type.hol_type
 type fixity = Term.fixity
 type term = Term.term
 type thm = Thm.thm
 type tactic = Abbrev.tactic

    val define_type = Def_MN_Type.define_type
    val define_mutual_functions = Def_MN_Func.define_mutual_functions
    val MUTUAL_INDUCT_THEN = MutualIndThen.MUTUAL_INDUCT_THEN

end;
