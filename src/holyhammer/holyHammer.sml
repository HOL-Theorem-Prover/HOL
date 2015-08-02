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

open hhWriter hhReconstruct

val ERR = mk_HOL_ERR "holyHammer"
val hh_dir = HOLDIR ^ "/src/holyhammer"
val scripts_dir = hh_dir ^ "/scripts"
val thy_dir = hh_dir ^ "/theories"

(* Settings *)

datatype PREDICTOR = KNN | Mepo | NBayes | Geo
datatype ATP = Eprover | Vampire | Z3

fun name_of_atp atp = case atp of
    Eprover => "eprover"
  | Vampire => "vampire"
  | Z3      => "z3"

fun name_of_predictor predictor = case predictor of
    KNN     => "knn"
  | Mepo    => "mepo"
  | NBayes  => "nbayes"
  | Geo     => "geo"

val eprover_settings = ref (KNN,128,5) 
val vampire_settings = ref (KNN,96,5)
val z3_settings  = ref (KNN,32,5)

fun change_time settings t =
  let val (p,n,_) = !settings in settings := (p,n,t) end

fun change_pred settings p =
  let val (_,n,t) = !settings in settings := (p,n,t) end

fun change_nbpred settings n =
  let val (p,_,t) = !settings in settings := (p,n,t) end

fun atp_settings atp = case atp of
    Eprover => !eprover_settings
  | Vampire => !vampire_settings
  | Z3      => !z3_settings

fun set_minimization b = minimize_flag := b

fun set_timeout time = 
  (
  change_time eprover_settings time;
  change_time vampire_settings time;
  change_time z3_settings time
  )

fun set_predictors pred = 
  (
  change_pred eprover_settings pred;
  change_pred vampire_settings pred;
  change_pred z3_settings pred
  )
 
fun reset_hh () =
  (
   eprover_settings := (KNN,128,5);
   vampire_settings := (KNN,96,5);
   z3_settings  := (KNN,32,5)
  )

fun set_prediction atp n = case atp of
    Eprover => change_nbpred eprover_settings n
  | Vampire => change_nbpred vampire_settings n
  | Z3      => change_nbpred z3_settings n

fun set_predictor atp pred = case atp of
    Eprover => change_pred eprover_settings pred
  | Vampire => change_pred vampire_settings pred
  | Z3      => change_pred z3_settings pred
 
(* Prover dependent names *)
fun dir_of_prover atp =
  let val atp_name = name_of_atp atp in
    hh_dir ^ "/provers/" ^ atp_name ^ "/" ^ atp_name ^ "_files"
  end

fun out_of_prover atp =
  let val atp_name = name_of_atp atp in
    dir_of_prover atp ^ "/" ^ atp_name ^ "_out"
  end

fun status_of_prover atp =
  let val atp_name = name_of_atp atp in
    dir_of_prover atp ^ "/" ^ atp_name ^ "_status"
  end

fun hh_of_prover atp = "hh_" ^ name_of_atp atp ^ ".sh"
  
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

fun mk_argl () =
  let 
    val (p1,n1,t1) = !eprover_settings
    val (p2,n2,t2) = !vampire_settings
    val (p3,n3,t3) = !z3_settings
    val predictorl = List.map name_of_predictor [p1,p2,p3]
    val nl         = List.map int_to_string [n1,n2,n3]
    val time       = int_to_string t1
  in
    String.concatWith " " (time :: (predictorl @ nl))
  end

fun prepare_cj thml cj =
  if null thml 
  then cj 
  else mk_imp (list_mk_conj (map (concl o GEN_ALL o DISCH_ALL) thml),cj)
 
(* Try every provers in parallel: eprover, vampire and z3. *)
fun hh thml cj =
  let
    val atpfilel = map (fn x => (status_of_prover x, out_of_prover x))
                   [Eprover,Vampire,Z3]
    val new_cj = prepare_cj thml cj
  in
    export new_cj;
    OS.Process.system 
      ("cd " ^ scripts_dir ^ "; " ^ "sh hh.sh " ^ mk_argl());
    reconstructl thml atpfilel cj
  end

(* Let you chose the specific prover you want to use either
   ("eprover", "vampire" or "z3") *)

fun hh_atp atp thml cj =
  let 
    val new_cj = prepare_cj thml cj
    val (p,n,t) = atp_settings atp
    val argl = name_of_predictor p ^ " " ^ int_to_string n ^ " " ^ 
               int_to_string t
  in
    export new_cj;
    OS.Process.system ("cd " ^ scripts_dir ^ "; " ^ "sh " ^ 
                         hh_of_prover atp ^ " " ^ 
                         argl);
    reconstruct thml (status_of_prover atp, out_of_prover atp) cj
  end


end
