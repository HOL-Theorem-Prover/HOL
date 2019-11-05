signature psBigSteps =
sig

  include Abbrev

  type ('a,'b) bigstepsparam =
    {
      mcts_param : ('a,'b) psMCTS.mctsparam,
      temp_flag : bool, 
      max_bigsteps : 'a -> int,
      verbose : bool,
      (* move to gamespec and gamevis *)
      string_of_move : 'b -> string,
      movel : 'b list,
      move_compare : ('b * 'b) -> order,
      string_of_board : 'a -> string
    }
  type id = psMCTS.id
  type ('a,'b) tree = ('a,'b) psMCTS.tree
  type 'b dis = ((('b * real) * id) * real) list
  type 'a ex = ('a * real list * real list)
  (* tree reuse *)
  val cut_tree : id -> ('a,'b) tree -> ('a,'b) tree

  (* todo: print policy-value instead *)
  val print_distrib : ('b -> string) -> 'b dis -> unit

  (* bigsteps *)
  val select_bigstep : ('a,'b) bigstepsparam -> ('a,'b) tree -> (id * 'b dis)
  val run_bigsteps : ('a,'b) bigstepsparam -> 'a -> 
    bool * 'a ex list * ('a, 'b) psMCTS.node list

end
