signature cv_typesLib =
sig
  include Abbrev

  (* manually add a from_to_theorem *)
  val add_from_to_thm    : thm -> unit

  (* returns a list of all from_to theorems *)
  val from_to_thms       : unit -> thm list

  (* automatically define new from/to functions for a user-defined datatype *)
  val define_from_to     : hol_type -> thm * thm * thm list

end