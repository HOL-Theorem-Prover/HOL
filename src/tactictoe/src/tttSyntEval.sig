signature tttSyntEval =
sig

  include Abbrev
  
  datatype role = Axiom | Theorem | Conjecture
  
  type idict_t = int * (term * (string, term) Redblackmap.dict)
  
  (* globals *)
  val nb_premises : int ref
   
  (* saving terms *)
  val export_tml : string -> term list -> unit
  val import_tml : string -> term list

  (* initialization *)
  val init_dicts : int ->
    (int list, term) Redblackmap.dict *
      (term, int list) Redblackmap.dict * 
      (term, role) Redblackmap.dict
  
  (* proving conjectures *)
  val prove_main : 
    (term, role) Redblackmap.dict ->
    string -> int -> int ->     
    (term -> term list) ->
    (string -> int -> term list * term -> idict_t) ->
    (string -> int -> int list -> int -> (int * string list option) list) ->
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
  val eval_main : string -> int -> int ->
    (int list, term) Redblackmap.dict * 
      (term, int list) Redblackmap.dict *
      (term, role) Redblackmap.dict ->
    (term -> term list) ->
    (string -> int -> term list * term -> idict_t) ->
    (string -> int -> int list -> int -> (int * string list option) list) ->
    ((term * term list) list * term list * term list)

 

end
