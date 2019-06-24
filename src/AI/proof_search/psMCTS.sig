signature psMCTS =
sig

  include Abbrev

  datatype status = Undecided | Win | Lose

  (* globals *)
  val exploration_coeff : real ref
  val temperature_flag : bool ref
  val alpha_glob : real ref
  val stopatwin_flag : bool ref

  (* debug *)
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
  type ('a,'b) mcts_param = 
    ( 
      int * real * bool *
      ('a sit -> status) * ('b -> 'a sit -> 'a sit) *
      ('a sit -> real * ('b * real) list)
    )
  val starttree_of : ('a,'b) mcts_param -> 'a sit -> ('a,'b) tree
  val mcts : ('a,'b) mcts_param -> ('a,'b) tree -> ('a,'b) tree
  val mcts_uniform : 
    int -> ('a sit -> status) * ('b -> 'a sit -> 'a sit) * 'b list -> 
    'a sit -> ('a,'b) tree

  (* dirichlet noise *)
  val gamma_distrib : real -> (real * real) list
  val dirichlet_noise : real -> int -> real list

  (* reuse previous search *)
  val cut_tree : ('a,'b) tree -> int list -> ('a,'b) tree

  (* statistics *)
  val backuptime : real ref
  val selecttime : real ref
  val root_variation : ('a,'b) tree -> (int list) list
  val max_depth : ('a,'b) tree -> int list -> int  
  val trace_one_win : 
    ('a sit -> status) -> ('a,'b) tree -> int list -> ('a,'b) node list

  (* constructing a training example *)
  val move_of_cid : ('a,'b) node -> int list -> 'b
  val evalpoli_example : ('a,'b) tree -> (real * ('b * real) list) option

  (* choosing a big step *)
  val print_distrib : ('b -> string) ->
    ((('b * real) * int list) * real) list -> unit
  val select_bigstep : ('a,'b) tree -> int list ->
    ('b choice * real) list * int list option


end
