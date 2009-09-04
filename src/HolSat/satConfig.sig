signature satConfig =
sig
    include Abbrev

type sat_config

val base_config : sat_config

val get_term : sat_config -> Term.term
val get_solver : sat_config -> SatSolvers.sat_solver
val get_infile : sat_config -> string option
val get_proof : sat_config -> string option
val get_flag_is_cnf : sat_config -> bool
val get_flag_is_proved : sat_config -> bool

val set_term : Term.term -> sat_config -> sat_config
val set_solver : SatSolvers.sat_solver -> sat_config -> sat_config
val set_infile : string -> sat_config -> sat_config
val set_proof : string -> sat_config -> sat_config
val set_flag_is_cnf : bool -> sat_config -> sat_config
val set_flag_is_proved : bool -> sat_config -> sat_config

val dest_config : sat_config -> (Term.term * SatSolvers.sat_solver * string option *
				 string option * bool * bool)

end
