signature tttLearn =
sig

  include Abbrev

  type thmdata = mlThmData.thmdata
  type call = mlTacticData.call
  type tacdata = mlTacticData.tacdata
  
  (* abstraction of theorem list arguments and first term in tactics *)
  val thmlarg_placeholder : string
  val is_thmlarg_stac : string -> bool 
  val abstract_thmlarg : string -> (string * string list list) option
  val inst_stac : string list -> string -> string
  
  val termarg_placeholder : string
  val is_termarg_stac : string -> bool 
  val abstract_termarg : string -> (string * string) option
  val apply_termarg_stac : string list -> string -> goal -> 
    ((goal list * validation) * string)
  val abstract_stac : string -> string option


  (* competition between different tactics over a goal *)
  val ortho_predstac_time : real ref
  val ortho_predthm_time : real ref
  val ortho_teststac_time : real ref
  val orthogonalize : (thmdata * tacdata) -> call -> call

end
