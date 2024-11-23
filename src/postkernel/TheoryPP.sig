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
 type thminfo = DB_dtype.thminfo
 type shared_writemaps = {strings : string -> int, terms : Term.term -> string}
 type shared_readmaps = {strings : int -> string, terms : string -> Term.term}
 type struct_info_record = {
   theory      : string*Arbnum.num*Arbnum.num,
   parents     : (string*Arbnum.num*Arbnum.num) list,
   types       : (string*int) list,
   constants   : (string*hol_type) list,
   all_thms    : (string * thm * thminfo) list,
   struct_ps   : (unit -> PP.pretty) option list,
   struct_pcps : (unit -> PP.pretty) list,
   mldeps      : string list,
   thydata     : string list * Term.term list *
                 (string,shared_writemaps -> HOLsexp.t)Binarymap.dict
 }

 val pp_type : string -> string -> hol_type -> PP.pretty

 val pp_sig_hook : (unit -> unit) ref

 val pp_sig : thm PP.pprinter ->
              {name        : string,
               parents     : string list,
               all_thms    : (string * thm * thminfo) list,
               sig_ps      : (unit -> PP.pretty) option list} PP.pprinter

 val pp_struct : struct_info_record PP.pprinter

 val pp_thydata : struct_info_record PP.pprinter

 val temp_binding : string -> string
 val is_temp_binding : string -> bool
 val dest_temp_binding : string -> string

end
