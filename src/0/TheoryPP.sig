signature TheoryPP =
sig

 type hol_type = Type.hol_type
 type thm      = Thm.thm
 type ppstream = Portable.ppstream

 type thm_printer = ppstream -> thm -> unit
 type type_printer = ppstream -> hol_type -> unit
 type HOLprinters = {pp_thm : thm_printer, pp_type : type_printer}

 (* prints the type to the ppstream in a form that could be read back in
    an interactive SML/HOL session, where the two string parameters are
    the names for the mk_vartype and mk_type functions respectively, where
    the types of the identifiers are as follows:
       string1 : string -> 'a
       string2 : string -> 'a list -> 'a
  *)
 val print_type_to_SML : string -> string -> ppstream -> hol_type -> unit


 val pp_theory_sig :
   thm_printer option -> ppstream ->
   {name        : string,
    parents     : string list,
    axioms      : (string * thm) list,
    definitions : (string * thm) list,
    theorems    : (string * thm) list,
    sig_ps      : (ppstream -> unit)option list} -> unit

 val pp_theory_struct :
   ppstream ->
   {theory      : string*int*int,
    parents     : (string*int*int) list,
    types       : (string*int) list,
    constants   : (string*hol_type) list,
    axioms      : (string * thm) list,
    definitions : (string * thm) list,
    theorems    : (string * thm) list,
    struct_ps   : (ppstream -> unit) option list} -> unit

end
