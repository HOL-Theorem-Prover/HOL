(*--------------------------------------------------------------------------*
 * This block of cheese keeps track of congruence rules that *aren't*       *
 * derived from a datatype definition.                                      *
 *                                                                          * 
 * In TFL, new notions of context come automatically from datatype          *
 * definitions, via case-definitions and their associated congruence rules, *
 * but the user can also add their own context notions by invoking          *
 * "Context.write_context", which takes a list of congruence rules and adds *
 * them to the data that Tfl uses when processing a definition.             *
 *--------------------------------------------------------------------------*)


structure Context :> Context =
struct

local val non_datatype_context = ref [Thms.LET_CONG, Thms.COND_CONG]
in
  fun read_context() = !non_datatype_context
  fun write_context L = (non_datatype_context := L)
end;

end
