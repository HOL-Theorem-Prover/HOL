(* ===================================================================== *)
(* FILE          : load_nested_rec_lib.sml                               *)
(* VERSION       : 0.0                                                   *)
(* DESCRIPTION   : Loads the nested_rec library, with an improved        *)
(*                 interface to define nested mutually recursive types,  *)
(*                 and tools to define new functions and prove theorems  *)
(*                 about them.                                           *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : April 21, 1998                                        *)
(* COPYRIGHT     : Copyright (c) 1998 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)


(* --------------------------------------------------------------------- *)
(* Load the nested recursive types definition library.                   *)
(* --------------------------------------------------------------------- *)
load_library_in_place (find_library "nested_rec");

(* --------------------------------------------------------------------- *)
(* Load the improved nested recursive types definition functors.         *)
(* --------------------------------------------------------------------- *)
use "define_mutual_types.sig";
use "mutrec.yak.sig";
use "mutrec.yak.sml";
use "define_mutual_types.sml";

(* --------------------------------------------------------------------- *)
(* Load the improved nested recursive functions definition tool.         *)
(* --------------------------------------------------------------------- *)
use "recftn.sml";
val define_mutual_functions = Recftn.define_mutual_functions;

(* --------------------------------------------------------------------- *)
(* Load the improved nested recursive types induction tactic.            *)
(* --------------------------------------------------------------------- *)
use "mutual_induct_then.sig";
use "mutual_induct_then.sml";
val MUTUAL_INDUCT_THEN = Mutual_induct_then.MUTUAL_INDUCT_THEN;

