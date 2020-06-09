signature mlFeature =
sig

  include Abbrev

  type fea = int list
  type symweight = (int, real) Redblackmap.dict
 
  (* set flag to false for constant features and to true for subterms features *)
  val sfea_of_term : bool -> term -> string list
  val sfea_of_goal : bool -> goal -> string list

  val fea_of_term : bool -> term -> fea
  val fea_of_term_mod : int -> bool -> term -> fea
  val fea_of_goal : bool -> goal -> fea

  val clean_goalsubfea_cache : unit -> unit
  val clean_goalcfea_cache : unit -> unit
  val fea_of_goal_cached : bool -> goal -> fea
  
  (* tfidf *)
  val learn_tfidf : ('a * fea) list -> symweight
  val learn_tfidf_res : (int, unit) Redblackmap.dict -> 
    ('a * fea) list -> symweight  

end
