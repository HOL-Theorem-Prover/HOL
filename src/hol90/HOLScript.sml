(* =====================================================================
 * FILE          : mk_HOL.sml
 * DESCRIPTION   : Make HOL theory by combining other theories.
 *
 * AUTHORS       : Donald Syme, University of Cambridge
 * DATE          : 95.10.21
 * ID            : $Id$
 *
 * ===================================================================== *)


structure HOLScript =
struct


(*---------------------------------------------------------------------------
 * Declare parent theory structures.
 *---------------------------------------------------------------------------*)
local open oneTheory sumTheory restr_binderTheory rec_typeTheory in end;

val _ = Parse.new_theory "HOL";
val _ = Parse.export_theory ();

end;
