
(* contains configuration info for HolSatLib that is independent of the SAT solver *)
(* SAT solver specific config is in SatSolver.sml *)
(* the main reason for having this as an opaque type is to give HolSatLib a stable signature *)
structure satConfig :> satConfig =
struct

local 

open Globals HolKernel Parse

in 

open SatSolvers Abbrev

type sat_config = 
     {
      pterm : term, (* input problem term *)
      solver: sat_solver, (* solver to use *)
      infile: string option, (* DIMACS input file; overrides pterm if SOME *)
      proof : string option, (* proof trace file in HolSatLib format; overrides solver if SOME*)
      flags : {is_cnf:bool,is_proved:bool} (* problem already in cnf, result is checked in HOL *)
     } 

val base_config = {pterm = boolSyntax.T, solver = minisatp, infile = NONE, proof = NONE, 
		   flags = {is_cnf=false,is_proved=true}}

(* getters *)

fun get_term (c:sat_config) = (#pterm c)

fun get_solver (c:sat_config) = (#solver c) 

(* if SOME, then valOf is name of cnf file on disk that is to be used directly *)
fun get_infile (c:sat_config) = (#infile c) 

(* if SOME, then valOf is name of proof file (HolSat format) on disk that is to be used directly *)
fun get_proof (c:sat_config) = (#proof c) 

(* if true, then we skip the def_cnf conversion. 
   if infile is SOME, then this is set to true *)
fun get_flag_is_cnf (c:sat_config) = #is_cnf (#flags c)

fun get_flag_is_proved (c:sat_config) = #is_proved (#flags c)

(* setters *)
fun set_term tm (c:sat_config) =    
    {pterm = tm, solver = #solver c, infile = #infile c, proof = #proof c, 
     flags = {is_cnf = #is_cnf (#flags c),is_proved = #is_proved (#flags c)}}

fun set_solver ss (c:sat_config) =    
    {pterm = #pterm c, solver = ss, infile = #infile c, proof = #proof c, 
     flags = {is_cnf = #is_cnf (#flags c),is_proved = #is_proved (#flags c)}}

fun set_infile nm (c:sat_config) = (* also sets is_cnf to true *)    
    {pterm = #pterm c, solver = #solver c, infile = SOME nm, proof = #proof c, 
     flags = {is_cnf = true,is_proved = #is_proved (#flags c)}}

fun set_proof nm (c:sat_config) = (* also sets is_cnf to true *)
     {pterm = #pterm c, solver = #solver c, infile = #infile c, proof = SOME nm, 
     flags = {is_cnf = true,is_proved = #is_proved (#flags c)}}

fun set_flag_is_cnf is (c:sat_config) = 
    {pterm = #pterm c, solver = #solver c, infile = #infile c, proof = #proof c, 
     flags = {is_cnf = is,is_proved = #is_proved (#flags c)}}

fun set_flag_is_proved ip (c:sat_config) = 
    {pterm = #pterm c, solver = #solver c, infile = #infile c, proof = #proof c,
     flags = {is_cnf = #is_cnf (#flags c),is_proved = ip}}

(* destruction (does not return flags) *)
fun dest_config c = (get_term c, get_solver c, get_infile c, get_proof c, 
		     get_flag_is_cnf c, get_flag_is_proved c)

end
end
