(* ===================================================================== *)
(* FILE          : type_def.sig                                          *)
(* DESCRIPTION   : Signature for the principle of type definition.       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Type_def =
sig

val new_type_definition : {name:string, pred:Term.term,
                           inhab_thm : Thm.thm} -> Thm.thm
end;
