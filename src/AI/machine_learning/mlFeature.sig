signature mlFeature =
sig

  include Abbrev

  type fea = int list

  val fea_of_term : term -> string list
  val fea_of_goal : goal -> string list

  val feahash_of_term : term -> fea
  val feahash_of_term_mod : int -> term -> fea
  
  val feahash_of_goal : goal -> fea
  val fea_of_goal_cached : goal -> fea
  val clean_goalfea_cache : unit -> unit

  (* tfidf *)
  val learn_tfidf : ('a * fea) list -> (int, real) Redblackmap.dict

end
