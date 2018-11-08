signature tttRobber =
sig
  
  include Abbrev
  
  type alltnn = 
    (tttNNtree.treenn * tttNNtree.treenn *
     tttNNtree.treenn * tttNNtree.treenn)
  
  type allex =  
    ((term * real) list * (term * real) list *
     (term * real) list * (term * real) list)

  (* Globals (used for constructing cuts) *)
  val initcut_glob : term ref
  val build_terms_glob : (term -> term list) ref
  val axl_glob     : term list ref
  val axl_glob2    : thm list ref
  val cutl_glob : term list ref
  val termsize_glob : int ref
  val lookup_flag  : bool ref
  val rewrite_flag : bool ref
  val rwcut_flag : bool ref

  (* Game configuration *)
  datatype cutter_board = 
    Board1 of goal * term option | Board2 of goal list 
  datatype cutter_move = 
    Forget of term | 
    InitCut of term | BuildCut of term | Cut of term | Rewrite of goal |
    Rwcut of goal list |
    Choice of goal 
  val p1_startpos : term -> cutter_board tttMCTS.pos  

  val is_primitive : goal -> bool

  (* policy and evaluation function *)
  val cutter_fevalpoli : 
    alltnn -> cutter_board tttMCTS.pos -> real * (cutter_move * real) list
  
  (* status function *)
  val cutter_status_of : cutter_board tttMCTS.pos -> tttMCTS.status

  (* apply_move function *)
  val cutter_apply_move : 
    cutter_move -> cutter_board tttMCTS.pos -> cutter_board tttMCTS.pos
  
  (* collecting examples from big steps *)
  (*
  val list_collect_exl : 
    int * real -> int -> (alltnn * allex) -> term list -> allex
  *)
  (* training a treenn *)
  val wrap_train_treenn : 
     int * (term * int) list -> (term * real) list -> tttNNtree.treenn

  (* reinforcement learning loop  *) 
  val rl_loop : 
    int * int ->
    int * real * int ->term list ->
    int * (term * int) list ->
    alltnn * allex ->         
    alltnn * allex


  val rl_gen : 
    int ->
    int * real * int -> term list ->
    int * (term * int) list ->
    alltnn * allex



end
