signature tttTermData =
sig

include Abbrev

  val export_tml : string -> term list -> unit
  val import_tml : string -> term list

end
