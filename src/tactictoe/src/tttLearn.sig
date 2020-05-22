signature tttLearn =
sig

  include Abbrev

  type thmdata = mlThmData.thmdata
  type call = mlTacticData.call
  type tacdata = mlTacticData.tacdata
  
  (* abstraction of theorem list arguments in tactics *)
  val thmlarg_placeholder : string
  val is_thmlarg_stac : string -> bool 
  val abstract_stac : string -> string option
  val inst_stac : string list -> string -> string
  
  (* competition between different tactics over a goal *)
  val ortho_predstac_time : real ref
  val ortho_predthm_time : real ref
  val ortho_teststac_time : real ref
  val orthogonalize : (thmdata * tacdata) -> call -> call

end
