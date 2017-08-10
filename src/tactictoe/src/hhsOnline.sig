signature hhsOnline =
sig

include Abbrev

val fetch_thm : string -> string -> string
val name_of_thm : thm -> string

end
