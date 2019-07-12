(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Premise selection and external provers                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure holyHammer :> holyHammer =
struct

open HolKernel boolLib Thread aiLib smlExecute smlRedirect smlParallel
  mlFeature mlThmData mlTacticData mlNearestNeighbor
  hhExportFof hhReconstruct hhTranslate hhTptp

val ERR = mk_HOL_ERR "holyHammer"
val debugdir = HOLDIR ^ "/src/holyhammer/debug"
fun debug s = debug_in_dir debugdir "holyHammer" s

(* -------------------------------------------------------------------------
   Settings
   ------------------------------------------------------------------------- *)

val timeout_glob = ref 10
fun set_timeout n = timeout_glob := n

(* -------------------------------------------------------------------------
   ATPs
   ------------------------------------------------------------------------- *)

datatype prover = Eprover | Z3 | Vampire
fun name_of atp = case atp of
    Eprover => "eprover"
  | Z3 => "z3"
  | Vampire => "vampire"

fun npremises_of atp = case atp of
    Eprover => 128
  | Z3 => 32
  | Vampire => 96

(* atps called by holyhammer if their binary exists *)
val all_atps = ref [Eprover,Z3,Vampire]

(* -------------------------------------------------------------------------
   Directories
   ------------------------------------------------------------------------- *)

val parallel_tag = ref ""

fun pathl sl = case sl of
    []  => raise ERR "pathl" "empty"
  | [a] => a
  | a :: m => OS.Path.concat (a, pathl m)

val hh_dir         = pathl [HOLDIR,"src","holyhammer"];

val provbin_dir    = pathl [hh_dir,"provers"];
fun provdir_of atp = pathl [provbin_dir,
  name_of atp ^ "_files" ^ (!parallel_tag)]
fun out_of atp     = pathl [provdir_of atp,"out"]
fun status_of atp  = pathl [provdir_of atp,"status"]

(* -------------------------------------------------------------------------
   Evaluation log
   ------------------------------------------------------------------------- *)

val hh_eval_dir    = pathl [hh_dir,"eval"];
val eval_flag = ref false
val eval_thy = ref "scratch"
fun log_eval s =
  if !eval_flag then
    let val file = hh_eval_dir ^ "/" ^ (!eval_thy) in
      mkDir_err hh_eval_dir;
      append_endline file s
    end
  else ()

(* -------------------------------------------------------------------------
   Run functions in parallel and terminate as soon as one returned a
   positive result in parallel_result.
   ------------------------------------------------------------------------- *)

val (parallel_result : string list option ref) = ref NONE

val attrib = [Thread.InterruptState Thread.InterruptAsynch, Thread.EnableBroadcastInterrupt true]

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

fun launch_atp dir atp t =
  let
    val cmd = "sh " ^ name_of atp ^ ".sh " ^ int_to_string t ^ " " ^
      dir ^ " > /dev/null 2> /dev/null"
    val _ = cmd_in_dir provbin_dir cmd
    val r = get_lemmas (status_of atp, out_of atp)
  in
    if isSome r
    then
      (
      atp_ref := name_of atp;
      print_endline ("proof found by " ^ name_of atp ^ ":");
      print_endline ("  " ^ mk_metis_call (valOf r));
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

val hh_goaltac_cache = ref (dempty goal_compare)

fun clean_hh_goaltac_cache () = hh_goaltac_cache := dempty goal_compare

(* Warning: limits the number of selected premises (even in hh_pb) *)
fun export_to_atp premises cj atp =
  let
    val new_premises = first_n (npremises_of atp) premises
    val namethml = thml_of_namel new_premises
  in
    fof_export_pb (provdir_of atp) (cj,namethml)
  end

fun exists_atp atp =
  exists_file (pathl [provbin_dir, name_of atp])

fun exists_atp_err atp =
  let val b = exists_file (pathl [provbin_dir, name_of atp]) in
    if not b then print_endline ("no binary for " ^ name_of atp) else ();
    b
  end

fun hh_pb wanted_atpl premises goal =
  let
    val _ = app (mkDir_err o provdir_of) wanted_atpl
    val atpl = filter exists_atp_err wanted_atpl
    val cj = list_mk_imp goal
    val _  = app (export_to_atp premises cj) atpl
    val t1 = !timeout_glob
    val t2 = Real.fromInt t1 + 2.0
    fun f x = fn () => ignore (launch_atp (provdir_of x) x t1)
    val olemmas = parallel_call t2 (map f atpl)
  in
    case olemmas of
      NONE =>
        (log_eval "  ATPs could not find a proof";
        raise ERR "hh_pb" "ATPs could not find a proof")
    | SOME lemmas =>
      let
        val (stac,tac) = hh_reconstruct lemmas goal
      in
        print_endline ("minimized proof:  \n  " ^ stac);
        log_eval ("  minimized proof:  \n    " ^ stac);
        hh_goaltac_cache := dadd goal (stac,tac) (!hh_goaltac_cache);
        tac
      end
  end

fun main_hh thmdata goal =
  let
    val atpl = filter exists_atp (!all_atps)
    val n = list_imax (map npremises_of atpl)
    val premises = thmknn_wdep thmdata n (feahash_of_goal goal)
  in
    hh_pb atpl premises goal
  end

fun has_boolty x = type_of x = bool
fun has_boolty_goal goal = all has_boolty (snd goal :: fst goal)


fun hh_goal goal =
  if not (has_boolty_goal goal)
  then raise ERR "hh_goal" "a term is not of type bool"
  else
    let val (stac,tac) = dfind goal (!hh_goaltac_cache) in
      print_endline ("goal already solved by:\n  " ^ stac);
      tac
    end
    handle NotFound => main_hh (create_thmdata ()) goal

fun hh_fork goal = Thread.fork (fn () => ignore (hh_goal goal), attrib)
fun hh goal = (hh_goal goal) goal
fun holyhammer tm = TAC_PROOF (([],tm), hh_goal ([],tm));

(* -------------------------------------------------------------------------
   HolyHammer evaluation without premise selection:
   trying to re-prove theorems from their dependencies.
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
      let val (_,t) = add_time (can (hh_pb atpl premises)) goal in
        log_eval ("  time: " ^ Real.toString t)
      end
  end

fun hh_pb_eval_thy atpl thy =
  (
  eval_flag := true; eval_thy := thy;
  mkDir_err hh_eval_dir;
  remove_file (hh_eval_dir ^ "/" ^ thy);
  app (hh_pb_eval_thm atpl) (DB.theorems thy);
  eval_flag := false; eval_thy := "scratch"
  )

(* -------------------------------------------------------------------------
   Usage:
     load "holyHammer"; load "gcdTheory"; open holyHammer;
     set_timeout 5;
     hh_pb_eval_thy [Eprover] "gcd";
   Results can be found in HOLDIR/src/holyhammer/eval.
  ------------------------------------------------------------------------- *)

fun eprover_pb_eval_extern (state: unit) (wid,job) thy =
  (
  parallel_tag := its wid;
  hh_pb_eval_thy [Eprover] thy
  )

fun eprover_pb_eval_parallel ncore timeout thyl =
  let
    fun write_state () = ()
    fun write_argl _ = ()
    fun read_result (wid,job) = ()
    val thyls =
      map (fn x => quote (x ^ "Theory")) (filter (fn x => x <> "min") thyl)
    val state_s =
      "(holyHammer.set_timeout " ^ its timeout ^ ";" ^
      " app load [" ^ String.concatWith "," thyls ^ "])"
    val argl_s = "[" ^ String.concatWith "," (map quote thyl) ^ "]"
    val f_s = "holyHammer.eprover_pb_eval_extern"
    fun code_of wid = standard_code_of (state_s,argl_s,f_s) wid
  in
    parmap_queue_extern ncore code_of (write_state, write_argl)
    read_result thyl
  end

(* -------------------------------------------------------------------------
   Usage:
     load "holyHammer"; open holyHammer;
     val ncore = 30;
     val timeout = 5;
     load "tttUnfold";
     tttUnfold.load_sigobj ();
     val thyl = ancestry (current_theory ());
     eprover_pb_eval_parallel ncore timeout thyl;
   Results can be found in HOLDIR/src/holyhammer/eval.
  ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Function called by the tactictoe evaluation framework
   ------------------------------------------------------------------------- *)

fun hh_eval (thmdata,tacdata) (thy,name) goal =
  let val tptpname = escape ("thm." ^ thy ^ "." ^ name) in
    eval_flag := true;
    eval_thy := current_theory ();
    mkDir_err hh_eval_dir;
    log_eval ("Theorem: " ^ tptpname);
    log_eval ("Goal: " ^ string_of_goal goal);
    ignore (main_hh thmdata goal);
    eval_flag := false; eval_thy := "scratch"
  end

(* -------------------------------------------------------------------------
   Usage:
     load "tttUnfold"; open tttUnfold; open tttSetup;
     ttt_hheval_flag := true;
     ttt_rewrite_thy "ConseqConv"; ttt_record_thy "ConseqConv";
     ttt_hheval_flag := false;
   Results can be found in HOLDIR/src/holyhammer/eval.
  ------------------------------------------------------------------------- *)


end (* struct *)
