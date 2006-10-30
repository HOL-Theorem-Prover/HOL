signature satConfig =
sig
    include Abbrev

type sat_config

val default_config : sat_config

val get_infile : sat_config -> string option
val get_flag_is_cnf : sat_config -> bool

val set_infile : string -> sat_config -> sat_config
val set_flag_is_cnf : bool -> sat_config -> sat_config

val dest_config : sat_config -> string option 

end
