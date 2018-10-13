signature tttRL =
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
  

  (* statistics *)
  (*
  datatype summary_t = 
    WinS | 
    LoseS | 
    Stats of (goal list * int * real * (string * real) list)

  val summary_of_tree : goal tree -> 
    ((summary_t list * real) * (real * (string * real) list))
  
  val variation_win : (term * summary_t list) * real -> bool  
  *)

  val preevalpoli_tm : tttNNtree.treenn -> term -> real * real list
  
  val string_of_trainset : (term * (real * real list)) list -> string
  
  val prepare_trainset : 
    (term * (real * real list)) list -> (term list * real vector) list
  
  (* tactic based search *)
  val tac_createdict : 
    (string * thm) list -> (string, tactic) Redblackmap.dict
  val tac_build_evalpoli : 
    (goal pos -> (real * real list)) ->
    string list -> 
    (int list -> goal pos -> real * choice list)
  val tac_mcts :
    (int list -> goal pos -> real * choice list) ->
    (string, tactic) Redblackmap.dict ->
    int -> term -> (term * goal tree)
  val play_n_move : 
     int -> (term * (goal tree)) list ->
     (int list -> goal pos -> real * choice list) ->
     (string, tactic) Redblackmap.dict ->
     int -> term -> (term * (goal tree)) list
    

  (* combining treenn with mcts *)
  val train_ngen :  
    int ->
    (term * int) list ->
    (string, tactic) Redblackmap.dict ->
    int -> int -> int -> int ->
    term list ->
    tttNNtree.treenn * (term * (real * real list)) list


end
