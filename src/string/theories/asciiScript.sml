(* =====================================================================*)
(* FILE		: mk_ascii.ml						*)
(* DESCRIPTION   : Creates a theory of 8-bit ascii character codes	*)
(* WRITES FILES	: ascii.th						*)
(*									*)
(* AUTHOR	: (c) T. Melham 1988					*)
(* DATE		: 87.07.27						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATED   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)
open HolKernel Parse Datatype;

val _ = new_theory "ascii";

(* ---------------------------------------------------------------------*)
(* define the type :ascii						*)
(* ---------------------------------------------------------------------*)

val _ = Hol_datatype
  `ascii = ASCII of bool=>bool=>bool=>bool=>bool=>bool=>bool=>bool`;


(*---------------------------------------------------------------------------

     For backwards compatibility : the Hol_datatype package invents
     its own names in a regular format, which differ in this case
     from the ones that the original author had.

 ---------------------------------------------------------------------------*)

val _ = adjoin_to_theory
{sig_ps = SOME (fn ppstrm =>
    let val S = PP.add_string ppstrm
        fun NL() = PP.add_newline ppstrm
    in
        S "(* For backward compatibility of theorem names *)"; NL();
        S "val ASCII_11        : thm"; NL()
    end),
 struct_ps = SOME(fn ppstrm =>
    let val S = PP.add_string ppstrm
        fun NL() = PP.add_newline ppstrm
    in
        S "(* For backward compatibility of theorem names *)"; NL();
        S "val ASCII_11        = ascii_11"; NL()
    end)};


val _ = export_theorems_as_docfiles "../help/thms" (theorems())
val _ = export_theorems_as_docfiles "../help/defs" (definitions())

val _ = export_theory();
