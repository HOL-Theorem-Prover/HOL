(* ========================================================================= *)
(* INTERFACE TO TPTP PROBLEM FILES                                           *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibTptp =
sig

type term    = mlibTerm.term
type formula = mlibTerm.formula

(* Maintaining different relation and function names in TPTP problems *)
val renaming : {tptp : string, fol : string, arity : int} list ref

(* Reading from a TPTP file in CNF/FOF format: pass in a filename *)
val read : {filename : string} -> formula

(* Writing to a TPTP file in CNF format: pass in a formula and filename *)
val write : {filename : string} -> formula -> unit

(* Making TPTP formulas more palatable *)
val prettify : formula -> formula

end
