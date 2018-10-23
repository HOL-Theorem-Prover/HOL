signature tttMCTS =
sig
  
  include Abbrev
  
  datatype status = Undecided | Win | Lose
  
  val string_of_status : status -> string

  (* 'a is the representation of the board *)  
  type 'a pos = bool * 'a

  (* ''b is the representation of a move *)
  type 'b choice = (('b * real) * int list)
  
  type ('a,'b) node = 
  {
    pol   : 'b choice list,
    pos   : 'a pos,
    id    : int list,
    sum   : real,
    vis   : real,
    status : status
  }

  type ('a,'b) tree = (int list, ('a,'b) node) Redblackmap.dict 

  (* tool *)
  val genealogy : int list -> int list list

  (* search function *)
  val mcts : 
    int ->
    ('a pos -> real * ('b * real) list) ->
    (('a,'b) tree -> 'a pos -> status) ->
    ('b -> 'a pos -> 'a pos) ->
    'a pos -> 
    ('a,'b) tree

  (* statistics *)
  val root_variation : ('a,''b) tree -> ('a,''b) node list
  
end
