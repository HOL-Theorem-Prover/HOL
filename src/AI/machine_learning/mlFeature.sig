signature mlFeature =
sig

  include Abbrev

  val fea_of_term : term -> string list
  val fea_of_goal : goal -> string list
  
  val feahash_of_term : term -> int list
  val feahash_of_goal : goal -> int list

end
