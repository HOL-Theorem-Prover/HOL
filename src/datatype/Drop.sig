signature Drop = 
sig
  include Abbrev

  val is_int_literal_hook      : (term -> bool) ref
  val is_string_literal_hook   : (term -> bool) ref
  val is_cons_hook             : (term -> bool) ref
  val is_list_hook             : (term -> bool) ref
  val dest_int_literal_hook    : (term -> Arbint.int) ref
  val dest_string_literal_hook : (term -> string) ref
  val dest_list_hook           : (term -> term list) ref

  val pp_type_as_ML : ppstream -> hol_type -> unit
  val pp_term_as_ML : ppstream -> term -> unit
  val pp_defn_as_ML : ppstream -> term -> unit
  val pp_datatype_as_ML : ppstream -> ParseDatatype.AST list -> unit

end
