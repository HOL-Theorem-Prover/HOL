signature psMCTS =
sig

  include Abbrev

  datatype status = Undecided | Win | Lose

  (* Debug *)
  val string_of_status : status -> string

  (* 'a is the representation of a board *)
  type 'a sit = bool * 'a

  (* ''b is the representation of a move *)
  type 'b choice = (('b * real) * int list)

  type ('a,'b) node =
  {
    pol   : 'b choice list,
    sit   : 'a sit,
    sum   : real,
    vis   : real,
    status : status
  }

  type ('a,'b) tree = (int list, ('a,'b) node) Redblackmap.dict

  (* search function *)
  val starttree_of :
    real ->
    (('a sit -> status) * ('b -> 'a sit -> 'a sit)) *
      ('a sit -> real * ('b * real) list) ->
    'a sit ->
    ('a,'b) tree

  val ignorestatus_flag : bool ref (* plain mcts *)

  val mcts :
    (int * real) ->
    (('a sit -> status) * ('b -> 'a sit -> 'a sit)) *
      ('a sit -> real * ('b * real) list) ->
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
  val move_of_cid : ('a,'b) node -> int list -> 'b
  val evalpoli_example : ('a,'b) tree -> (real * real list) option

  (* choosing a big step *)
  val select_bigstep : ('a,'b) tree -> int list -> int list option

end
