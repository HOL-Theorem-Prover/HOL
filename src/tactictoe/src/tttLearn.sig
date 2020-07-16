signature tttLearn =
sig

  include Abbrev

  type thmdata = mlThmData.thmdata
  type call = mlTacticData.call
  type tacdata = mlTacticData.tacdata
  type symweight = mlFeature.symweight

  (* abstraction of theorem list arguments and first term in tactics *)
  val tactictoe_thmlarg : thm list
  val thmlarg_placeholder : string
  val is_thmlarg_stac : string -> bool
  val abstract_thmlarg : string -> (string * string list list) option
  val thmls_of_thmidl : string list -> string
  val inst_thmlarg : string -> string -> string

  val termarg_placeholder : string
  val is_termarg_stac : string -> bool
  val abstract_termarg : string -> (string * string) option
  val inst_termarg : goal -> string -> string
  val abstract_stac : string -> string option
  val inst_stac : (string * goal) -> string -> (string * string) option
  val inst_stacl : (string list * goal) -> string list -> (string * string) list

  (* competition between different tactics over a goal *)
  val ortho_predstac_time : real ref
  val ortho_predthm_time : real ref
  val ortho_teststac_time : real ref
  val orthogonalize : (thmdata * tacdata *
    (symweight * (string * mlFeature.fea) list)) ->
    call -> call

end
