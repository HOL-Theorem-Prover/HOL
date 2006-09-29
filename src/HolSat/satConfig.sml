
(* contains configuration info for HolSatLib that is independent of the SAT solver *)
(* SAT solver specific config is in SatSolver.sml *)
(* the main reason for having this as an opaque type is to give HolSat
   a stable signature *)
structure satConfig :> satConfig =
struct

local 

open Globals HolKernel Parse

in 

open Abbrev

type sat_config = 
     {
      infile: string option,
      flags: {is_cnf:bool}
     } 

val default_config = {infile = NONE, flags = {is_cnf=false}}

(* getters *)

(* if SOME, then valOf is name of cnf file on disk that is to be used directly *)
fun get_infile (c:sat_config) = (#infile c) 

(* if true, then we skip the defCNF conversion. 
   if infile is SOME, then this is set to true *)
fun get_flag_is_cnf (c:sat_config) = #is_cnf (#flags c)

(* setters *)
fun set_infile nm (c:sat_config) = (* also sets is_cnf to true *)    
    {infile = SOME nm, flags = {is_cnf = true}}

fun set_flag_is_cnf is (c:sat_config) = 
    if isSome (#infile c) 
    then failwith "Error setting satconfig.is_cnf: sat_config.infile is set\n"
    else {infile = #infile c, flags = {is_cnf = is}}


(* destruction (does not return flags) *)

fun dest_config c = (get_infile c,get_flag_is_cnf c)

end
end
