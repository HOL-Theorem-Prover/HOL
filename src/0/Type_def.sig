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

(* this function now has the zero appended to the name to avoid clashes
   with the function of the same name defined in Parse, which calls this
   function and also updates the type grammar to cause things to print
   properly. *)
val new_type_definition0 : {name:string, pred:Term.term,
                           inhab_thm : Thm.thm} -> Thm.thm
end;
