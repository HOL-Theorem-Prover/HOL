signature TheoryPP =
sig

 type hol_type = Type.hol_type
 type fixity   = Term.fixity
 type thm      = Thm.thm
 type ppstream = Portable_PrettyPrint.ppstream 

 val pp_theory_sig 
   : ppstream -> {name        : string,
                  parents     : string list,
                  axioms      : (string * thm) list,
                  definitions : (string * thm) list,
                  theorems    : (string * thm) list,
                  sig_ps      : (ppstream -> unit)option list} -> unit
      
 val pp_theory_struct 
   : ppstream -> {theory      : string*int*int,
		  parents     : (string*int*int) list,
		  types       : (string*int) list,
                  constants   : (string*hol_type*fixity) list,
                  axioms      : (string * thm) list,
                  definitions : (string * thm) list,
                  theorems    : (string * thm) list,
                  struct_ps   : (ppstream -> unit) option list} -> unit

end
