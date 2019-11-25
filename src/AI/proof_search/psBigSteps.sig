signature psBigSteps =
sig

  include Abbrev


  (* tree *)
  type id = psMCTS.id
  type ('a,'b) node = ('a,'b) psMCTS.node
  type ('a,'b) tree = ('a,'b) psMCTS.tree

  (* reinforcement learning examples *)
  type 'a rlex = ('a * real list * real list) list

  (* tree reuse *)
  val cut_tree : id -> ('a,'b) tree -> ('a,'b) tree

  (* bigsteps *)
  type ('a,'b) bigsteps_obj =
    {
    verbose : bool,
    temp_flag : bool,
    max_bigsteps : 'a -> int,
    mcts_obj : ('a,'b) psMCTS.mcts_obj
    }

  val select_bigstep :
    ('a,'b) bigsteps_obj -> ('a,'b) tree -> id
  val run_bigsteps :
    ('a,'b) bigsteps_obj -> 'a ->
    bool * 'a rlex * ('a,'b) psMCTS.node list

end
