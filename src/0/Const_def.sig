(* ===================================================================== *)
(* FILE          : const_def.sig                                         *)
(* DESCRIPTION   : Signature for three variants on the principle of      *)
(*                 definition. Translated from hol88.                    *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Const_def =
sig

  val new_gen_definition
    : {name:string,
       def : Term.term,
       fixity : Term.fixity} -> Thm.thm

  val new_definition        : string * Term.term -> Thm.thm
  val new_infix_definition  : string * Term.term * int -> Thm.thm
  val new_binder_definition : string * Term.term -> Thm.thm
 
  val define_exists : unit -> Thm.thm
end
