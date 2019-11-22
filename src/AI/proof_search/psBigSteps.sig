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
  type ('a,'b,'c) bigsteps_obj =
    {
    verbose : bool,
    temp_flag : bool,
    max_bigsteps : 'a -> int,
    precomp : 'a -> 'c,
    preplayer : 'c -> ('a,'b) psMCTS.player,
    game : ('a,'b) psMCTS.game,
    mcts_param : psMCTS.mcts_param
    }

  val run_bigsteps :
    ('a,'b,'c) bigsteps_obj -> 'a -> bool * 'a rlex * ('a,'b) node list

end
