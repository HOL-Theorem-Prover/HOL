(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Export types, constants, theorems and dependencies to *)
(*                 the holyHammer framework which performs premise       *)
(*                 selection and calls to external provers. The lemmas   *)
(*                 found by the provers is reconstructed with Metis.     *)                 
(*                                                                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure holyHammer :> holyHammer =
struct

open hhWriter

val ERR = mk_HOL_ERR "holyHammer"
val hh_dir = HOLDIR ^ "/src/holyhammer"
val scripts_dir = hh_dir ^ "/scripts"
val thy_dir = hh_dir ^ "/theories"

fun dir_of_prover prover = 
  hh_dir ^ "/provers/" ^ prover ^ "/" ^ prover ^ "_files"
fun out_of_prover prover = 
  dir_of_prover prover ^ "/" ^ prover ^ "_out"
fun status_of_prover prover = 
  dir_of_prover prover ^ "/" ^ prover ^ "_status"
fun hh_of_prover prover = "hh_" ^ prover ^ ".sh"
val list_of_provers = ["eprover","vampire","z3"]

(* Export object from the loaded theories *)
fun export cj =
  let 
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct  
  in
    OS.Process.system ("cd " ^ scripts_dir ^ "; " ^ "sh hh_clean.sh");
    (* write loaded theories *)
    write_hh_thyl thy_dir thyl;
    (* write the conjecture in thf format *)
    write_conjecture (thy_dir ^ "/conjecture") cj;
    (* write the dependencies between theories *)
    write_thydep (thy_dir ^ "/thydep") thyl
  end

(* Try every provers in parallel: eprover, vampire and z3. *)
fun hh cj =
  let 
    val atpfilel = map (fn x => (status_of_prover x, out_of_prover x))
                   list_of_provers
  in
    export cj;
    (* call holyhammer and the external provers *)
    OS.Process.system ("cd " ^ scripts_dir ^ "; " ^ "sh hh.sh");        
    (* try to rebuild the proof found using metis *)
    replay_atpfilel atpfilel cj
  end

(* Let you chose the specific prover you want to use either 
   (eprover, vampire or z3) *)
fun hh_atp prover cj =
  if not (mem prover list_of_provers) 
  then raise ERR "hh_prover" "not supported prover"
  else
    (
    export cj;
    (* call holyhammer and one external prover *)
    OS.Process.system ("cd " ^ scripts_dir ^ "; " ^ "sh " ^ hh_of_prover prover);
    (* try to rebuild the proof found using metis *)
    replay_atpfile (status_of_prover prover, out_of_prover prover) cj
    )

end
