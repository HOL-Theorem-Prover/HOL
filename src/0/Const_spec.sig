(* ===================================================================== *)
(* FILE          : const_spec.sig                                        *)
(* DESCRIPTION   : Signature for the principle of constant specification.*)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Const_spec =
sig

val new_specification :
  {name :string, consts : string list, sat_thm : Thm.thm} -> Thm.thm
end;
