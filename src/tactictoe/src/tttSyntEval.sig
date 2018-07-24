signature tttSyntEval =
sig

  include Abbrev
  
  datatype role = Axiom | Theorem | Reproven | Conjecture
  datatype usage = Irrelevant | Predicted | Useful of term list
  
  val dict_glob :
    (int * (int * int), (term * int list) * role) Redblackmap.dict ref

  val revtm_glob : (term, (int * (int * int)) * (string * thm) * role) 
    Redblackmap.dict ref

  val update_dict: (string, int) Redblackmap.dict -> string -> unit
  
  val mprove : term list -> term -> bool
  val minimize_aux : term list -> term list -> term -> term list
  val miniprove : term list -> term -> term list option
  
  val prove_cj : 
    (int, real) Redblackmap.dict * (term * int list) list ->
    term -> (term * term list) option
  
  val eval_cjl  : (term * term list) list -> (usage * term) list
  
  val reprove : (int * (int * int)) * ((term * int list) * role) -> unit
  
  val init_n_thy : int -> unit
  
  (* statistics *)
  val is_useful : usage -> bool
  val is_predicted : usage -> bool
  
end
