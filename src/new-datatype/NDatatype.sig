signature NDatatype =
sig
  include Abbrev

  val Datatype : hol_type quotation -> thm list

end
