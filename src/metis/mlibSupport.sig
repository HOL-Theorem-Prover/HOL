(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

signature mlibSupport =
sig

type id_clause = mlibClauseset.id_clause

type parameters = {size_power : real, literal_power : real}

val defaults             : parameters
val update_size_power    : (real -> real) -> parameters -> parameters
val update_literal_power : (real -> real) -> parameters -> parameters

type sos

val empty  : parameters -> sos
val reset  : sos -> sos
val size   : sos -> int
val add    : real -> id_clause list -> sos -> sos
val remove : sos -> ((real * id_clause) * sos) option

end
