signature Opentheory = sig
  type thms   = Thm.thm Net.net
  type types  = (string, Type.hol_type list -> Type.hol_type) Redblackmap.dict
  type consts = (string, Type.hol_type -> Term.term) Redblackmap.dict
  val empty_thms     : thms
  val empty_types    : types
  val empty_consts   : consts
  val thmsFromList   : Thm.thm list -> thms
  val typesFromList  : (string * (Type.hol_type list -> Type.hol_type)) list -> types
  val constsFromList : (string * (Type.hol_type -> Term.term)) list -> consts
  val read_article   : TextIO.instream -> {thms:thms,types:types,consts:consts} -> Thm.thm list
end
