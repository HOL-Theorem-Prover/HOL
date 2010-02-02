(*---------------------------------------------------------------------------*
 * MODULE      : TheoryPP                                                    *
 * DESCRIPTION : HOL theories represented by SML structures.                 *
 * AUTHOR      : Konrad Slind                                                *
 * DATE        : 1998                                                        *
 *---------------------------------------------------------------------------*)

signature TheoryPP =
sig
 type thm
 type hol_type
 type ppstream = Portable.ppstream
 type num = Arbnum.num

 val pp_type : string -> string -> ppstream -> hol_type -> unit

 val pp_sig
   : (ppstream -> thm -> unit)
     -> {name        : string,
         parents     : string list,
         axioms      : (string * thm) list,
         definitions : (string * thm) list,
         theorems    : (string * thm) list,
         sig_ps      : (ppstream -> unit) option list}
     -> ppstream
     -> unit

 val pp_struct
   : {theory      : string*num*num,
      parents     : (string*num*num) list,
      types       : (string*int) list,
      constants   : (string*hol_type) list,
      axioms      : (string * thm) list,
      definitions : (string * thm) list,
      theorems    : (string * thm) list,
      thydata     : (string,string)Binarymap.dict,
      struct_ps   : (ppstream -> unit) option list}
   -> ppstream
   -> unit

end
