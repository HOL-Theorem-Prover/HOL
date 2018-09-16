signature tttSyntEval =
sig

  include Abbrev
  
  datatype role = Axiom | Theorem
  
  type idict_t = int * (term * (string, term) Redblackmap.dict)
  
  (* initialization *)
  val init_dicts : unit ->
    (int list, term) Redblackmap.dict *
      (term, int list) Redblackmap.dict * 
      (term, role) Redblackmap.dict

  (* re-proving theorems *)
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

 

end
