signature psBigSteps =
sig

  include Abbrev

  (* tree reuse *)
  val cut_tree : id -> ('a,'b) tree -> ('a,'b) tree

  (* training example *)
  val evalpoli_example : ('a,'b) tree -> (real * ('b * real) list)

  (* bigsteps *)
  val print_distrib : ('b -> string) -> 'b dis -> unit
  val select_bigstep : ('a,'b) tree -> (id * 'b dis)

end
