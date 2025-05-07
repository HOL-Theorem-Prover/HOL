signature abstraction =
sig

  include Abbrev

  val add_parameter : term -> unit

  val get_assums : unit -> term list
  val set_assums : term list -> unit
  val add_assums : term list -> unit

  val gen_assums : thm -> thm

  val add_impl_param : string -> term list -> unit
  val impl_of : string -> Absyn.absyn list

  val param_eq : term -> term

  (*----------------------*)
  type inst_infos =
    { Vals : term list,
      Inst : thm list,
      Rule : thm -> thm,
      Rename : string -> string option }

  type cinst_infos

  val compute_inst_infos : term list -> inst_infos -> cinst_infos
  val inst_thm_fun : cinst_infos -> thm -> thm
  val IMPORT : inst_infos -> term list -> (string * thm) list ->
               thm Symtab.table
  val IMPORT_THY : inst_infos -> string -> thm Symtab.table
  val thyTerms : {thyname:string} -> term list
  val record_terms : term list -> unit

end
