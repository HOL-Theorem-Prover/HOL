(*---------------------------------------------------------------------------*
 * This block of cheese keeps track of congruence rules that aren't derived  *
 * from a datatype definition.                                               *
 *---------------------------------------------------------------------------*)

structure Context :> Context =
struct

local val non_datatype_context = ref []:Thm.thm list ref
in
  fun read_context() = !non_datatype_context
  fun write_context L = (non_datatype_context := L)
end;

end
