(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

signature mlibSupport =
sig

type 'a pp = 'a mlibUseful.pp

type parameters = {size_power : real, literal_power : real}

val defaults             : parameters
val update_size_power    : (real -> real) -> parameters -> parameters
val update_literal_power : (real -> real) -> parameters -> parameters

type sos

val empty   : parameters -> sos
val reset   : sos -> sos
val size    : sos -> int
val add     : real * mlibClause.clause list -> sos -> sos
val remove  : sos -> ((real * mlibClause.clause) * sos) option
val to_list : sos -> mlibClause.clause list
val pp_sos  : sos pp

end
