(* ========================================================================= *)
(* A STORE IN WHICH TO CACHE UNIT THEOREMS                                   *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibUnits =
sig

type 'a pp   = 'a mlibUseful.pp
type formula = mlibTerm.formula
type thm     = mlibThm.thm

type units

val empty      : units
val add        : thm -> units -> units
val addl       : thm list -> units -> units
val subsumes   : units -> formula -> thm option
val contr      : units -> thm -> thm option
val prove      : units -> formula list -> thm list option
val demod      : units -> thm -> thm
val info       : units -> string
val pp_units   : units pp

end
