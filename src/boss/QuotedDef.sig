signature QuotedDef =
sig


  type term     = Term.term
  type thm      = Thm.thm
  type defn     = Defn.defn
  type 'a quotation = 'a Portable.frag list

  val Hol_fun : string -> term quotation -> defn 
  val xDefine : string -> term quotation -> thm
  val Define  : term quotation -> thm

  val ind_suffix : string ref
  val def_suffix : string ref

end;
