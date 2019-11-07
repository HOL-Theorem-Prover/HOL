signature psBigSteps =
sig

  include Abbrev


  (* tree *)
  type id = psMCTS.id
  type ('a,'b) node = ('a,'b) psMCTS.node
  type ('a,'b) tree = ('a,'b) psMCTS.tree
  
  (* machine learning examples *)
  type 'b dis = ((('b * real) * id) * real) list
  type 'a ex = ('a * real list * real list)

  (* tree reuse *)
  val cut_tree : id -> ('a,'b) tree -> ('a,'b) tree

  (* bigsteps *)
  type ('a,'b,'c) bigsteps_param =
    {
    verbose : bool,
    temp_flag : bool, 
    max_bigsteps : 'a -> int,
    mcts_param : ('a,'b) psMCTS.mcts_param,
    (* parallelization *)
    write_param : string -> 'c -> unit,
    read_param : string -> 'c,
    write_targetl : string -> 'a list -> unit,
    read_targetl : string -> 'a list,
    write_result : string -> bool * 'a ex list -> unit,
    read_result : string -> bool * 'a ex list
    }

  val select_bigstep : ('a,'b,'c) bigsteps_param -> ('a,'b) tree -> (id * 'b dis)
  val run_bigsteps : ('a,'b,'c) bigsteps_param -> 'a -> 
    bool * 'a ex list * ('a,'b) psMCTS.node list

  (* parallelization *)
  val ext_bigsteps : ('a,'b,'c) bigsteps_param -> 'c -> 'a -> 
    bool * 'a ex list
  val bigsteps_to_extspec : string -> ('a,'b,'c) bigsteps_param -> 
    ('c, 'a, bool * 'a ex list) smlParallel.extspec

  val para_bigsteps : 
    int -> ('a, 'b, bool * 'd) smlParallel.extspec ->
    'a -> 'b list -> (bool * 'd) list


end
