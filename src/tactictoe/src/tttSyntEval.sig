signature tttSyntEval =
sig

  include Abbrev
  
  datatype role = Axiom | Theorem | Conjecture
  
  type idict_t = int * (term * (string, term) Redblackmap.dict)

  (* initialization *)
  val init_dicts : int ->
    (int list, term) Redblackmap.dict *
      (term, int list) Redblackmap.dict * 
      (term, role) Redblackmap.dict
  
  (* statistics on conjecture generation *)
  val write_subdict : 
    ((term * term) list, term list * real) Redblackmap.dict -> unit
  val write_origindict :
    (term, ((term * term) list * term) list) Redblackmap.dict -> unit

  (* proving conjectures *)
  val prove_main : int -> int ->     
    (int -> term list * term -> idict_t) ->
    (int -> int list -> int -> (int * string list option) list) ->
    term list -> (* theorems *)
    term list -> (* conjectures *)
    (term * term list) list
  
  (* updating dictionnaries *)
  val insert_cjl : 
    (int list, term) Redblackmap.dict * 
      (term, int list) Redblackmap.dict *
      (term, role) Redblackmap.dict ->
    (term * term list) list ->
    (int list, term) Redblackmap.dict * 
      (term, int list) Redblackmap.dict *
      (term, role) Redblackmap.dict

  (* evaluating conjecture *)
  val eval_main : int -> int ->
    (int list, term) Redblackmap.dict * 
      (term, int list) Redblackmap.dict *
      (term, role) Redblackmap.dict ->
    (int -> term list * term -> idict_t) ->
    (int -> int list -> int -> (int * string list option) list) ->
    (term * term list) list

 

end
