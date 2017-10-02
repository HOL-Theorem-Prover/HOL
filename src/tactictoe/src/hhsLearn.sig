signature hhsLearn =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
 
  val create_solved : lbl_t list -> (goal, int) Redblackmap.dict
  val orthogonalize : lbl_t list -> feav_t -> lbl_t
  
  val succ_cthy_dict : (string,(int * int)) Redblackmap.dict ref
  val succ_glob_dict : (string,(int * int)) Redblackmap.dict ref
  val count_try      : string -> unit
  val count_succ     : string -> unit
  val inv_succrate   : string -> real
  
  val succrate_reader : (string * (int * int)) list ref
  val import_succrate : string list -> (string * (int * int)) list
  val export_succrate : string -> unit

end
