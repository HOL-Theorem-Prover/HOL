(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

signature mlibSupport =
sig

type clause    = mlibClause.clause

type parameters = {size_bias : int}
val defaults : parameters

type sos

val new    : parameters -> sos
val reset  : sos -> sos
val size   : sos -> int
val add    : clause -> sos -> sos
val addl   : clause list -> sos -> sos       (* These get the same timestamp *)
val remove : sos -> (clause * sos) option

end