(* =====================================================================*)
(* FILE		: mk_string.ml						*)
(* DESCRIPTION  : Creates the theory `string.th`.			*)
(*									*)
(* PARENTS	: ascii.th						*)
(* WRITES FILES	: string.th						*)
(*									*)
(* AUTHOR	: (c) T. Melham 1988					*)
(* DATE		: 87.07.27						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATED   : Konrad Slind, University of Calgary                   *)
(* REVISED      : Konrad Slind, University of Cambridge Dec 1998        *)
(*                (to use Hol_datatype package)                         *)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)
(* open HolKernel Parse Prim_rec Define_type ConstrProofs asciiTheory; *)

open HolKernel Parse Datatype asciiTheory;


val _ = new_theory "string";


(* ---------------------------------------------------------------------*)
(* define the type :string (and a lot more) 			        *)
(* ---------------------------------------------------------------------*)

val string_info = 
 Datatype.primHol_datatype 
   (TypeBase.theTypeBase())  `string = emptystring  (* empty string *)
                                     | STRING of ascii => string`;


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
        S "val string_Induct    : thm"; NL();
        S "val string_CASES     : thm"; NL();
        S "val STRING_11        : thm"; NL();
        S "val NOT_STRING_EMPTY : thm"
    end),
 struct_ps = SOME(fn ppstrm => 
    let val S = PP.add_string ppstrm
        fun NL() = PP.add_newline ppstrm
    in
        S "(* For backward compatibility of theorem names *)"; NL();
        S "val string_Induct    = string_induction"; NL();
        S "val string_CASES     = string_nchotomy"; NL();
        S "val STRING_11        = string_11"; NL();
        S "val NOT_STRING_EMPTY = string_distinct"; NL();
        NL();
        S "val _ = Globals.assert_strings_defined();"
    end)};

val _ = export_theory();
