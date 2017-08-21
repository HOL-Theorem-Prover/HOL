(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Export types, constants, theorems and dependencies to *)
(*                 the holyHammer framework which performs premise       *)
(*                 selection and calls to external provers. The lemmas   *)
(*                 found by the provers help Metis to reconstruct the    *)
(*                 proof.                                                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure holyHammer :> holyHammer =
struct

open HolKernel boolLib hhWriter hhReconstruct

val ERR = mk_HOL_ERR "holyHammer"

fun cmd_in_dir dir cmd =
  OS.Process.system ("cd " ^ dir ^ "; " ^ cmd);

(*---------------------------------------------------------------------------
   Settings
 ----------------------------------------------------------------------------*)

val timeout_glob = ref 5

fun set_minimization b = minimize_flag := b
fun set_timeout n = timeout_glob := n

(*---------------------------------------------------------------------------
   Directories
 ----------------------------------------------------------------------------*)

val hh_dir = HOLDIR ^ "/src/holyhammer"
val scripts_dir = hh_dir ^ "/scripts"
val thy_dir = hh_dir ^ "/theories"

fun dir_of_prover atp = hh_dir ^ "/provers/" ^ name_of_atp atp ^ "_files"

fun out_of_prover atp =
  dir_of_prover atp ^ "/" ^ name_of_atp atp ^ "_out"

fun status_of_prover atp =
  dir_of_prover atp ^ "/" ^ name_of_atp atp ^ "_status"

fun hh_of_prover atp = "hh_" ^ name_of_atp atp ^ ".sh"

(*---------------------------------------------------------------------------
   Export
 ----------------------------------------------------------------------------*)

fun export_problem premises cj =
  let
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct
  in
    (* write loaded theories *)
    write_premises thy_dir premises thyl;
    (* write the conjecture in thf format *)
    write_conjecture (thy_dir ^ "/conjecture") cj;
    (* write the dependencies between theories *)
    write_thydep (thy_dir ^ "/thydep") thyl
  end

(*---------------------------------------------------------------------------
   Main functions
 ----------------------------------------------------------------------------*)

(* Try every provers in parallel: eprover, vampire and z3. *)
fun hh_argl cj argl =


fun hh cj =
  (
  cmd_in_dir scripts_dir "sh hh_clean.sh";
  let
    val atpfilel = 
      map (fn x => (status_of_prover x, out_of_prover x) proverl
    
    val premises = thmknn_ext
  in
    
    export_problem cj;
    cmd_in_dir scripts_dir ("sh hh.sh " ^ argl);
    app (fun x => reconstruct x cj) 
  end
  
  
  hh_argl cj
  )
  
fun hh_wo_pred predl atp thml cj =
  let
    val new_cj = prepare_cj thml cj
    val (p,n,t) = atp_settings atp
    val argl = "all 0 " ^ int_to_string t
    val _ = cmd_in_dir scripts_dir "sh hh_clean.sh"
    val _ = export_wo_pred predl new_cj
    val (_,tim) = hhs_add_time (cmd_in_dir scripts_dir) 
      ("sh " ^ hh_of_prover atp ^ " " ^ argl);
  in
    append_file (HOLDIR ^ "/hh_rep") ("proof time: " ^ Real.toString tim);
    reconstruct_wo_pred (status_of_prover atp, out_of_prover atp) new_cj
  end  

fun hh_goal (asl,w) = hh (list_mk_imp (asl,w))


end
