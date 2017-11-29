signature hhsLearn =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
 
  (* number of steps to solve the goal: use for smart subsumption *)
  val create_solved : lbl_t list -> (goal, int * int) Redblackmap.dict
  
  (* orthogonalization *)
  val orthogonalize : lbl_t list -> feav_t -> lbl_t

  (* abstraction *)
  val abstract_stac : string -> string
  val inst_stac     : string -> string -> string
  val is_pattern_stac : string -> bool

end
