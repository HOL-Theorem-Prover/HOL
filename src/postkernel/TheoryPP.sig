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
   theory      : string,
   parents     : (string*string) list,
   types       : (string*int) list,
   constants   : (string*hol_type) list,
   all_thms    : (string * thm * thminfo) list,
   mldeps      : string list,
   thydata     : string list * Term.term list *
                 (shared_writemaps -> HOLsexp.t) Symtab.table
 }
 type sig_info_record = {
   name        : string,
   parents     : {name : string, url : string} list,
   types       : (string * int) list,
   constants   : (string * hol_type) list,
   all_thms    : (string * thm * thminfo) list
 }

 val pp_type : string -> string -> hol_type -> PP.pretty

 val pp_sig : {name        : string,
               parents     : string list,
               all_thms    : (string * thm * thminfo) list} PP.pprinter

 val print_doc_html :
     {pp_thm : thm PP.pprinter, pp_type : hol_type PP.pprinter} ->
     sig_info_record -> TextIO.outstream -> unit

 val write_script_html : {script_path : string, out_path : string} -> unit


 val pp_struct : string -> struct_info_record PP.pprinter

 val pp_thydata : struct_info_record PP.pprinter

 val temp_binding : string -> string
 val is_temp_binding : string -> bool
 val dest_temp_binding : string -> string

end
