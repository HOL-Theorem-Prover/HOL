signature hhsOpen =
sig

  include Abbrev

  val all_values : string -> (string list * string list * string list)
  val all_structures : string -> string list
  
end
