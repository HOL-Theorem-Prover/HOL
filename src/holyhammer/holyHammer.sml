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

val exported_thyl = ref []

(*---------------------------------------------------------------------------
   Settings
 ----------------------------------------------------------------------------*)

datatype PREDICTOR = KNN | Mepo | NBayes | Geo | Kepo
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
  | Kepo    => "kepo"

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

fun export cj =
  let
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct
  in
    (* write loaded theories *)
    write_hh_thyl thy_dir thyl;
    (* write the conjecture in thf format *)
    write_conjecture (thy_dir ^ "/conjecture") cj;
    (* write the dependencies between theories *)
    write_thydep (thy_dir ^ "/thydep") thyl
  end

(*---------------------------------------------------------------------------
   Main helpers
 ----------------------------------------------------------------------------*)

fun mk_argl (e_settings,v_settings,z_settings) =
  let
    val (p1,n1,t1) = e_settings
    val (p2,n2,t2) = v_settings
    val (p3,n3,t3) = z_settings
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

fun cmd_in_dir dir cmd =
  OS.Process.system ("cd " ^ dir ^ "; " ^ cmd);

(*---------------------------------------------------------------------------
   Main functions
 ----------------------------------------------------------------------------*)

(* Try every provers in parallel: eprover, vampire and z3. *)
fun hh_argl thml cj argl =
  let
    val atpfilel = map (fn x => (status_of_prover x, out_of_prover x))
                   [Eprover,Vampire,Z3]
    val new_cj = prepare_cj thml cj
  in
    cmd_in_dir scripts_dir "sh hh_clean.sh";
    export new_cj;
    cmd_in_dir scripts_dir ("sh hh.sh " ^ argl);
    reconstructl atpfilel new_cj
  end

fun hh thml cj =
  hh_argl thml cj
    (mk_argl (!eprover_settings,!vampire_settings,!z3_settings))

(* Try best strategies sequentially *)
fun hh_try thml cj time =
  let
    val negcj  = mk_neg cj
    val strat1 = ((KNN,128,time),(KNN,96,time),(KNN,32,time))
    val strat2 = ((Mepo,128,time),(Mepo,96,time),(Mepo,32,time))
    val strat3 = ((KNN,128*2,time),(KNN,96*2,time),(KNN,32*2,time))
    val strat4 = ((Mepo,128*2,time),(Mepo,96*2,time),(Mepo,32*2,time))
  in
    (print "Try KNN ...\n"; hh_argl thml cj (mk_argl strat1)) handle _ =>
    (print "Try Mepo ...\n"; hh_argl thml cj (mk_argl strat2)) handle _ =>
    (print "Doubling the number of predictions\n";
     print "Try KNN ...\n"; hh_argl thml cj (mk_argl strat3)) handle _ =>
    (print "Try Mepo ...\n"; hh_argl thml cj (mk_argl strat4)) handle _ =>
    (print "Proving the negation ...\n";
     hh_argl thml (mk_neg cj) (mk_argl strat1))
  end

(* Let you chose the specific prover you want to use either *)
fun hh_atp atp thml cj =
  let
    val new_cj = prepare_cj thml cj
    val (p,n,t) = atp_settings atp
    val argl = name_of_predictor p ^ " " ^ int_to_string n ^ " " ^
               int_to_string t
  in
    cmd_in_dir scripts_dir "sh hh_clean.sh";
    export new_cj;
    cmd_in_dir scripts_dir ("sh " ^ hh_of_prover atp ^ " " ^ argl);
    reconstruct (status_of_prover atp, out_of_prover atp) new_cj
  end

(* Derived function *)
fun hh_goal thml (goal as (tml,tm)) = hh thml (list_mk_imp (tml,tm))


end
