signature tttSyntEval =
sig

  include Abbrev
  
  datatype role = Axiom | Theorem | Conjecture

  type idict_t = (int * (term * (string, term) Redblackmap.dict))  

  (* initialization *)
  val dict_glob :
    (int list, (term * int list) * role) Redblackmap.dict ref
  val revtm_glob : (term, int list * (string * thm) * role) 
    Redblackmap.dict ref
  val update_dict : (string, int) Redblackmap.dict -> string -> unit
  val init_n_thy : int -> unit
  
  (* proving conjectures *)
  val pred_trans_write_cjl : 
    (int, real) Redblackmap.dict * (term * int list) list ->
    (int -> term list * term -> idict_t) -> 
    term list -> 
    idict_t list
  
  (* evaluating conjecture *)
  val eval_pred_trans_write : 
    (int -> term list * term -> idict_t) -> 
    (term * term list) list -> 
    idict_t list

  (* test *)
  val is_conjecture : term -> bool
  val is_nontrivial : 'a list option -> bool

  (* *)
  val read_result : 
    (int * (term * (string, term) Redblackmap.dict)) list ->
    (int * string list option) list -> (term * term list option) list
  
end
