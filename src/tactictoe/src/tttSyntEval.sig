signature tttSyntEval =
sig

  include Abbrev
  
  datatype role = Axiom | Theorem
  
  type idict_t = int * (term * (string, term) Redblackmap.dict)
  
  val one_in_n : int -> int -> 'a list -> 'a list
  
  (* initialization *)
  val init_dicts : unit -> (term, (int list * role)) Redblackmap.dict
  
  (* generate conjectures and estimates the coverage *)
  val targeted_conjectures :  
    int ->
    (term, (int list * role)) Redblackmap.dict -> unit

  (* re-proving theorems *)
  (* 
  val reprove : int -> (int -> term list -> term list) ->
           (string ->
             int ->
               term list * term -> int * (term * ('a, term) Redblackmap.dict))
             ->
             (string -> int -> int list -> 'b -> (int * 'a list option) list)
               ->
               string ->
                 int ->
                   'b ->
                     'c * (term, int list) Redblackmap.dict *
                     (term, role) Redblackmap.dict -> term list
   *)
   val cj_target :
      term list -> term -> unit


end
