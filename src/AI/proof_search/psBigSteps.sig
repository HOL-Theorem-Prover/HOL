signature psBigSteps =
sig

  include Abbrev


  (* tree *)
  type id = psMCTS.id
  type ('a,'b) node = ('a,'b) psMCTS.node
  type ('a,'b) tree = ('a,'b) psMCTS.tree

  (* reinforcement learning examples *)
  type 'a rlex = ('a * real list) list

  (* tree reuse *)
  val cut_tree : id -> ('a,'b) tree -> ('a,'b) tree

  (* bigsteps *)
  type ('a,'b) bsobj =
    {
    verbose : bool,
    temp_flag : bool,
    player : ('a,'b) psMCTS.player,
    game : ('a,'b) psMCTS.game,
    mctsparam : psMCTS.mctsparam
    }

  val run_bigsteps : ('a,'b) bsobj -> 'a -> bool * 'a rlex * ('a,'b) node list

end
