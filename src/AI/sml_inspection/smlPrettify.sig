signature smlPrettify =
sig

  include Abbrev

  val elim_par : string list -> string list
  val elim_infix : string list -> string list
  val elim_struct : string list -> string list
  val elim_dbfetch : string list -> string list

  val requote : string list -> string list

  val smart_space : string list -> string

end
