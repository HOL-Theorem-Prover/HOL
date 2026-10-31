signature Refute_ForlSat = sig
  val configured_sat_solvers : bool -> string list
  val smart_sat_solver_name : bool -> string
  val sat_solver_spec : Time.time -> string -> string * string list
end
