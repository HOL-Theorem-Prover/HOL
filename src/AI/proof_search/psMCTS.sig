signature psMCTS =
sig
  
  include Abbrev
  
  datatype status = Undecided | Win | Lose
  
  (* Debug *)
  (*
  val log : string -> unit
  val summary : string -> unit
  val erase_log : unit -> unit
  *)
  val string_of_status : status -> string
  
  (* 'a is the representation of the board *)  
  type 'a pos = bool * 'a

  (* ''b is the representation of a move *)
  type 'b choice = (('b * real) * int list)
  
  type ('a,'b) node = 
  {
    pol   : 'b choice list,
    pos   : 'a pos,
    sum   : real,
    vis   : real,
    status : status
  }

  type ('a,'b) tree = (int list, ('a,'b) node) Redblackmap.dict 

  (* search function *)
  val starttree_of :     
    real ->
    ('a pos -> real * ('b * real) list) ->
    ('a pos -> status) ->
    'a pos -> 
    ('a,'b) tree

  val mcts : 
    (int * real) ->
    ('a pos -> real * ('b * real) list) ->
    ('a pos -> status) ->
    ('b -> 'a pos -> 'a pos) ->
    ('a,'b) tree -> 
    ('a,'b) tree
  
  (* restart *)
  val cut_tree : ('a,'b) tree -> int list -> ('a,'b) tree

  (* statistics *)
  val backuptime : real ref
  val selecttime : real ref
  datatype wintree = Wleaf of int list | Wnode of (int list * wintree list)
  val wtree_of : ('a,'b) tree -> int list -> wintree  
  val root_variation : ('a,'b) tree -> (int list) list

  (* constructing a training example *)
  val policy_example : ('a,'b) tree -> int list -> (int list * real) list
  (* choosing a big step *)
  val select_bigstep : ('a,'b) tree -> int list -> int list option

end
