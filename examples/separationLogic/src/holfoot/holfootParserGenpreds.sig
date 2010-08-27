signature holfootParserGenpreds =
sig
  include Abbrev

  val reset_genpreds             : unit -> unit
  val add_default_genpreds       : unit -> unit
  val init_genpreds              : unit -> unit

end
