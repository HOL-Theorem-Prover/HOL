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

  (* abstraction of tactic arguments *)
  val abstract_stac   : string -> string option
  val inst_stac       : string -> goal -> string -> string
  val is_absarg_stac  : string -> bool

end
