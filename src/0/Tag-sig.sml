(* ===================================================================== *)
(* FILE          : Tag.sig                                               *)
(* DESCRIPTION   : Theorem tagging (for oracles and other stuff)         *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : 1998                                                  *)
(* MODIFIED      : July 2000, Konrad Slind                               *)
(* ===================================================================== *)

signature Tag =
sig
     type tag

     val read   : string -> tag
     val merge  : tag -> tag -> tag
     val pp_tag : Portable.ppstream -> tag -> unit

end 
