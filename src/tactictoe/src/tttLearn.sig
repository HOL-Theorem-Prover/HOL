signature tttLearn =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  (* orthogonalization *)
  val orthogonalize : feav_t -> lbl_t

  (* abstraction of terms *)
  val abs_termarg : string ->
    (term * (term quotation -> tactic)) option
  val inst_termarg :  string -> term -> string

  (* abstraction of tactic arguments *)
  val abstract_stac   : string -> string option
  val inst_stac       : string -> goal -> string -> string
  val is_absarg_stac  : string -> bool

end



