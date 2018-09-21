signature tttFeature =
sig

  include Abbrev
  val syntfea_of_term : term -> int list
  val fea_of_term : term -> string list
  val fea_of_goal : goal -> int list
  val fea_of_goallist : goal list -> int list
  val hash_string : string -> int
  val hash_term : term -> int
  val hash_goal : goal -> int

end
