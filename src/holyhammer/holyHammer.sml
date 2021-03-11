(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Premise selection and external provers                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure holyHammer :> holyHammer =
struct

open HolKernel boolLib Thread aiLib 
  smlExecute smlRedirect smlParallel smlTimeout
  mlFeature mlThmData mlTacticData mlNearestNeighbor
  hhExportFof hhReconstruct hhTranslate hhTptp

val ERR = mk_HOL_ERR "holyHammer"

(* -------------------------------------------------------------------------
   Settings
   ------------------------------------------------------------------------- *)

val timeout_glob = ref 10
fun set_timeout n = timeout_glob := n

val dep_flag = ref false

(* -------------------------------------------------------------------------
   ATPs
   ------------------------------------------------------------------------- *)

datatype prover = Eprover | Z3 | Vampire
fun name_of atp = case atp of
    Eprover => "eprover"
  | Z3 => "z3"
  | Vampire => "vampire"

fun npremises_of atp =
  if !dep_flag then 100000 else
  case atp of
    Eprover => 128
  | Z3 => 32
  | Vampire => 96

(* ATPs called by holyhammer if their binary exists *)
val all_atps = ref [Eprover,Z3,Vampire]

(* -------------------------------------------------------------------------
   Directories
   ------------------------------------------------------------------------- *)

fun pathl sl = case sl of
    []  => raise ERR "pathl" "empty"
  | [a] => a
  | a :: m => OS.Path.concat (a, pathl m)

val hhdir = pathl [HOLDIR,"src","holyhammer"]
val bindir = pathl [hhdir,"provers"]
fun fof_dir dir atp = pathl [dir, name_of atp ^ "_files"]

(* ---------------------------------------------------------------------------
   Evaluation log
   ------------------------------------------------------------------------- *)

val hh_eval_dir = pathl [hhdir,"eval"];
val eval_flag = ref false
val eval_thy = ref "scratch"
fun log_eval s =
  if !eval_flag then
    let val file = hh_eval_dir ^ "/" ^ (!eval_thy) in
      mkDir_err hh_eval_dir;
      append_endline file s
    end
  else print_endline s

(* ---------------------------------------------------------------------------
   Run functions in parallel and terminate as soon as one returned a
   positive result in parallel_result.
   ------------------------------------------------------------------------- *)

val (parallel_result : string list option ref) = ref NONE

val attrib = [Thread.InterruptState Thread.InterruptAsynch, 
  Thread.EnableBroadcastInterrupt true]

fun parallel_call t fl =
  let
    val _ = parallel_result := NONE
    fun rec_fork f = Thread.fork (fn () => f (), attrib)
    val threadl = map rec_fork fl
    val rt = Timer.startRealTimer ()
    fun loop () =
      (
      OS.Process.sleep (Time.fromReal 0.01);
      if isSome (!parallel_result) orelse
         not (exists Thread.isActive threadl) orelse
         Timer.checkRealTimer rt  > Time.fromReal t
      then (app interruptkill threadl; !parallel_result)
      else loop ()
      )
  in
    loop ()
  end

(* -------------------------------------------------------------------------
   Launch an ATP
   ------------------------------------------------------------------------- *)

val atp_ref = ref ""

fun launch_atp fofdir atp t =
  let
    val cmd = "sh " ^ name_of atp ^ ".sh " ^ int_to_string t ^ " " ^
      fofdir ^ " > /dev/null 2> /dev/null"
    val _ = cmd_in_dir bindir cmd
    val r = get_lemmas (fofdir ^ "/status", fofdir ^ "/out")
  in
    if isSome r
    then
      (
      atp_ref := name_of atp;
      log_eval ("  proof found by " ^ name_of atp ^ ":");
      log_eval ("    " ^ mk_metis_call (valOf r));
      parallel_result := r
      )
    else ();
    r
  end

(* -------------------------------------------------------------------------
   HolyHammer
   ------------------------------------------------------------------------- *)

fun export_to_atp dir premises cj atp =
  let
    val new_premises = first_n (npremises_of atp) premises
    val namethml = hidef thml_of_namel new_premises
    val fofdir = fof_dir dir atp
    val _ = mkDir_err fofdir
  in
    fof_export_pb fofdir (cj,namethml)
  end

fun exists_atp atp =
  exists_file (pathl [bindir, name_of atp])

fun exists_atp_err atp =
  let val b = exists_file (pathl [bindir, name_of atp]) in
    if not b then print_endline ("no binary for " ^ name_of atp) else ();
    b
  end

fun hh_pb dir wanted_atpl premises goal =
  let
    val atpl = filter exists_atp_err wanted_atpl
    val cj = list_mk_imp goal
    val _  = app (export_to_atp dir premises cj) atpl
    val t1 = !timeout_glob
    val t2 = Real.fromInt t1 + 2.0
    fun f x = fn () => ignore (launch_atp (fof_dir dir x) x t1)
    val olemmas = parallel_call t2 (map f atpl)
  in
    case olemmas of
      NONE =>
        (log_eval "  ATPs could not find a proof";
        raise ERR "hh_pb" "ATPs could not find a proof")
    | SOME lemmas =>
      let
        val (stac,tac) = hidef (hh_reconstruct lemmas) goal
      in
        log_eval ("  minimized proof:  \n    " ^ stac);
        tac
      end
  end

fun main_hh dir thmdata goal =
  let
    val atpl = filter exists_atp (!all_atps)
    val _ =
      if null atpl
      then raise ERR "main_hh" "no ATP binary: see src/holyhammer/README"
      else ()
    val n = list_imax (map npremises_of atpl)
    val premises = thmknn_wdep thmdata n (fea_of_goal true goal)
  in
    hh_pb dir atpl premises goal
  end

fun has_boolty x = type_of x = bool
fun has_boolty_goal goal = all has_boolty (snd goal :: fst goal)

fun hh_goal goal =
  if not (has_boolty_goal goal)
  then raise ERR "hh_goal" "a term is not of type bool"
  else
    let val thmdata = hidef create_thmdata () in
      main_hh bindir thmdata goal
    end

fun hh_fork goal = Thread.fork (fn () => ignore (hh_goal goal), attrib)
fun hh goal = let val tac = hh_goal goal in hidef tac goal end
fun holyhammer tm = hidef TAC_PROOF (([],tm), hh_goal ([],tm));

(* -------------------------------------------------------------------------
   HolyHammer evaluation without premise selection:
   trying to re-prove theorems from their dependencies
   ------------------------------------------------------------------------- *)

fun hh_pb_eval_thm atpl (s,thm) =
  let
    val _ = print_endline ("\nTheorem: " ^ s)
    val _ = log_eval ("\nTheorem: " ^ s)
    val goal = dest_thm thm
    val (b,premises) = intactdep_of_thm thm
    val _ = log_eval ("  dependencies:\n    " ^
      (String.concatWith "\n    " premises))
  in
    if not b then (print_endline "  broken_dependencies (not tested)";
                   log_eval "  broken dependencies (not tested)")
    else
      let val (_,t) = add_time (can (hh_pb bindir atpl premises)) goal in
        log_eval ("  time: " ^ Real.toString t)
      end
  end

fun hh_pb_eval_thy atpl thy =
  (
  dep_flag := true; eval_flag := true; eval_thy := thy;
  mkDir_err hh_eval_dir;
  remove_file (hh_eval_dir ^ "/" ^ thy);
  app (hh_pb_eval_thm atpl) (DB.theorems thy);
  dep_flag := false; eval_flag := false; eval_thy := "scratch"
  )

(* -------------------------------------------------------------------------
   Function called by the tactictoe evaluation framework
   ------------------------------------------------------------------------- *)

(*
fun hh_eval expdir (thy,n) (thmdata,tacdata) nnol goal =
  let val b = !hide_flag in
    hide_flag := false; 
    mkDir_err hh_eval_dir;
    log_eval ("Goal: " ^ string_of_goal goal);
    ignore (main_hh thmdata goal);
    eval_flag := false; hide_flag := b;
    eval_thy := "scratch"
  end
*)

end (* struct *)
