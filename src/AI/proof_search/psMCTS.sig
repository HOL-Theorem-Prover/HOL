signature psMCTS =
sig

  include Abbrev

  (* outcome *)
  datatype status = Undecided | Win | Lose

  (* 'a is the representation of a board *)
  (* 'b is the representation of a move *)
  type id = int list
  type 'b pol = (('b * real) * id) list
  type 'b dis = ((('b * real) * id) * real) list
  type ('a,'b) node =
    {pol : 'b pol, sit : 'a, sum : real, vis : real, status : status}
  type ('a,'b) tree = (id, ('a,'b) node) Redblackmap.dict

  (* dirichlet noise *)
  val gamma_distrib : real -> (real * real) list
  val dirichlet_noise : real -> int -> real list

  (* search function *)
  type ('a,'b) mctsparam =
    {
    nsim : int, 
    stopatwin_flag : bool,
    decay : real,
    explo_coeff : real,
    noise_flag : bool,
    noise_coeff : real,
    noise_alpha : real,
    status_of : 'a -> status,
    apply_move : 'b -> 'a -> 'a,
    fevalpoli : 'a -> real * ('b * real) list
    }
  val starttree_of : ('a,'b) mctsparam -> 'a -> ('a,'b) tree
  val mcts : ('a,'b) mctsparam -> ('a,'b) tree -> ('a,'b) tree

  (* statistics *)
  val root_variation : ('a,'b) tree -> id list
  val max_depth : ('a,'b) tree -> id -> int
  val trace_win : ('a -> status) -> ('a,'b) tree -> id -> ('a,'b) node list

end
