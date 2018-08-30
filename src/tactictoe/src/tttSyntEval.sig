signature tttSyntEval =
sig

  include Abbrev
  
  datatype role = Axiom | Theorem | Reproven | Conjecture
  datatype usage = Irrelevant | Predicted of term list | Useful of term list
  
  val dict_glob :
    (int list, (term * int list) * role) Redblackmap.dict ref

  val revtm_glob : (term, int list * (string * thm) * role) 
    Redblackmap.dict ref
  
  val update_dict : (string, int) Redblackmap.dict -> string -> unit
  val init_n_thy : int -> unit
  
  val prove : 
    (string -> int -> term list -> term -> term list option) ->
     int ->
     (int, real) Redblackmap.dict * (term * int list) list ->
     string * term -> (term * term list option)
  
  val filter_nontrivial : 
    term * term list option -> (term * term list) option
  
  val parallel_eval : 
    (string -> int -> term list -> term -> term list option) -> 
    int -> int -> (term * term list) list -> (usage * term) list

  val is_useful : usage -> bool
  val is_predicted : usage -> bool
  
end
