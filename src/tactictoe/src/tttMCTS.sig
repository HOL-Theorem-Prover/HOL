signature tttMCTS =
sig
  
  include Abbrev

  type 'a pos = bool * 'a list option
  type choice = (string * real * int list)
  
  type 'a node = 
  {
    pol   : choice list,
    pos   : 'a pos,
    id    : int list,
    sum   : real ref,
    vis   : real ref
  }
  type 'a tree = (int list, 'a node) Redblackmap.dict 

  datatype endcheck = InProgress | Win | Lose 
  
  (* search function *)
  val mcts : 
    int ->
    (int list -> 'a pos -> real * choice list) ->
    ('a pos -> endcheck) ->
    (string -> 'a pos -> 'a pos) ->
    'a pos -> 
    'a tree
  
  (* creating a player *)
  val rand_evalpoli : string list -> 'a pos -> (real * real list)
  val wrap_poli : int list -> ('a * 'b) list -> ('a * 'b * int list) list
  
  (* training examples *)
  val traineval_of_node : 'a node -> real
  val trainpoli_of_node : 'a tree -> 'a node -> (string * real) list
  val trainex_of_node   : 'a tree -> 'a node -> (real * real list) 

  (* statistics *)
  val main_variation : 'a tree -> 'a node list
  

end
