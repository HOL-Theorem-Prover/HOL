signature QuotedDef =
sig

  type term     = Term.term
  type thm      = Thm.thm
  type defn     = Defn.defn
  type tactic   = Abbrev.tactic
  type 'a quotation = 'a Portable.frag list

  val ind_suffix : string ref
  val def_suffix : string ref

  val Hol_fun    : string -> term quotation -> defn 
  val xDefine    : string -> term quotation -> thm
  val Define     : term quotation -> thm

end;
