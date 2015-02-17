(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Export types, constants, theorems and dependencies to *)
(*                 the holyHammer framework which performs premise       *)
(*                 selection and calls to external provers. The proof    *)
(*                 found by the provers is reconstructed with Metis.     *)
(*                                                                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure holyHammer :> holyHammer =
struct

open thfWriter

val hh_dir = HOLDIR ^ "/src/holyhammer"
val thy_dir = hh_dir ^ "/theories"
val eprover_dir = hh_dir ^ "/provers/eprover/eprover_files"
val vampire_dir = hh_dir ^ "/provers/vampire/vampire_files"
val z3_dir      = hh_dir ^ "/provers/z3/z3_files"
val all_out     = [eprover_dir ^ "/eprover_out",
                   vampire_dir ^ "/vampire_out",
                   z3_dir ^ "/z3_out"]
val all_status  = [eprover_dir ^ "/eprover_status",
                   vampire_dir ^ "/vampire_status",
                   z3_dir ^ "/z3_status"]

(* Try every provers if they exists in the order: eprover, vampire and z3. *)
fun holyhammer cj =
  let 
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct  
  in
    OS.Process.system ("cd " ^ hh_dir ^ "; sh hh_clean.sh"); 
    (* write loaded theories *)
    write_thf_thyl thy_dir thyl; 
    (* write the conjecture in thf format *)
    write_conjecture (thy_dir ^ "/conjecture") cj;
    (* call holyhammer and the external provers *)
    OS.Process.system ("cd " ^ hh_dir ^ "; sh hh.sh"); 
    (* try to rebuild the proof found using metis *)
    replay_atpfilel all_status all_out cj
  end

(* Let you chose the specific prover you want to use either 
   (eprover, vampire or z3) *)
fun hh_prover prover cj =
  let 
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct  
  in
    OS.Process.system ("cd " ^ hh_dir ^ "; sh hh_clean.sh"); 
    (* write loaded theories *)
    write_thf_thyl thy_dir thyl;
    (* write the conjecture in thf format *)
    write_conjecture (thy_dir ^ "/conjecture") cj;
    (* call holyhammer and one external prover *)
    case prover of 
      "eprover" => OS.Process.system ("cd " ^ hh_dir ^ "; sh hh_eprover.sh")
    | "vampire" => OS.Process.system ("cd " ^ hh_dir ^ "; sh hh_vampire.sh")
    | "z3"      => OS.Process.system ("cd " ^ hh_dir ^ "; sh hh_z3.sh")
    ; 
    (* try to rebuild the proof found using metis *)
    replay_atpfilel all_status all_out cj
  end


end
