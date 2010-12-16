(*---------------------------------------------------------------------------*
 * MODULE      : TheoryPP                                                    *
 * DESCRIPTION : HOL theories represented by SML structures.                 *
 * AUTHOR      : Konrad Slind                                                *
 * DATE        : 1998                                                        *
 *---------------------------------------------------------------------------*)

signature TheoryPP =
sig
 type thm = Thm.thm
 type hol_type = Type.hol_type
 type ppstream = Portable.ppstream

 val pp_type : string -> string -> ppstream -> hol_type -> unit

 val pp_sig_hook : (unit -> unit) ref  (* XXX minimal change to make HOL build *)

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
   : {theory      : string*Arbnum.num*Arbnum.num,
      parents     : (string*Arbnum.num*Arbnum.num) list,
      types       : (string*int) list,
      constants   : (string*hol_type) list,
      axioms      : (string * thm) list,
      definitions : (string * thm) list,
      theorems    : (string * thm) list,
      struct_ps   : (ppstream -> unit) option list,
      thydata     : (string,string)Binarymap.dict}
   -> ppstream
   -> unit

end
