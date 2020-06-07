(* ========================================================================= *)
(* FILE          : tttEval.sml                                               *)
(* DESCRIPTION   : Evaluation framework for TacticToe                        *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttEval :> tttEval =
struct

open HolKernel Abbrev boolLib aiLib 
  smlRedirect smlParallel smlOpen tttSetup tttSearch tacticToe

val ERR = mk_HOL_ERR "tttEval"

(* -------------------------------------------------------------------------
   Evaluation function
   ------------------------------------------------------------------------- *)

fun print_status r = case r of
   ProofSaturated => print_endline "tactictoe: saturated"
 | ProofTimeout   => print_endline "tactictoe: timeout"
 | Proof s        => print_endline ("tactictoe: proven\n  " ^ s)

fun ttt_eval (thmdata,tacdata) goal =
  let
    val b = !hide_flag
    val _ = hide_flag := false
    val _ = print_endline ("ttt_eval: " ^ string_of_goal goal)
    val _ = print_endline ("ttt timeout: " ^ rts (!ttt_search_time))
    val (status,t) = add_time (main_tactictoe (thmdata,tacdata)) goal
  in
    print_status status;
    print_endline ("ttt_eval time: " ^ rts_round 6 t ^ "\n");
    hide_flag := b
  end

(* ------------------------------------------------------------------------
   Evaluation: requires recorded savestates.
   The recorded savestates can be produced by setting ttt_savestate_flag
   before calling tttUnfold.ttt_clean_record () and tttUnfold.ttt_record ().
   Warnings: 
   - requires ~10-100 GB of hard disk space. 
   - possibly avoid using MLTON during configuration.
   ------------------------------------------------------------------------ *)

fun sreflect_real s r = ("val _ = " ^ s ^ " := " ^ rts (!r) ^ ";")
fun sreflect_flag s flag = ("val _ = " ^ s ^ " := " ^ bts (!flag) ^ ";")

fun write_evalscript prefix file =
  let
    val file1 = mlquote (file ^ "_savestate")
    val file2 = mlquote (file ^ "_goal")
    val sl =
    ["PolyML.SaveState.loadState " ^ file1 ^ ";",
     "val tactictoe_goal = mlTacticData.import_goal " ^ file2 ^ ";",
     "load " ^ mlquote "tttEval" ^ ";",
     sreflect_real "tttSetup.ttt_search_time" ttt_search_time,
     sreflect_real "tttSetup.ttt_policy_coeff" ttt_policy_coeff,
     sreflect_real "tttSetup.ttt_explo_coeff" ttt_explo_coeff,
     sreflect_flag "tttSetup.thml_explo_flag" thml_explo_flag,
     sreflect_flag "aiLib.debug_flag" debug_flag,
     "tttEval.ttt_eval " ^
     "(!tttRecord.thmdata_glob, !tttRecord.tacdata_glob) " ^
     "tactictoe_goal;"]
  in
    writel (file ^ "_eval.sml") sl
  end

fun bare file = OS.Path.base (OS.Path.file file)

fun run_evalscript dir file =
  (
  write_evalscript (bare file) file;
  run_buildheap_nodep dir (file ^ "_eval.sml")
  )

fun run_evalscript_thyl expname b ncore thyl =
  let
    val dir = ttt_eval_dir ^ "/" ^ expname ^ (if b then "" else "_tenth")
    val _ = (mkDir_err ttt_eval_dir; mkDir_err dir)
    val thyl' = filter (fn x => not (mem x ["min","bool"])) thyl
    val pbl = map (fn x => tactictoe_dir ^ "/savestate/" ^ x ^ "_pbl") thyl'
    fun f x = (readl x handle Interrupt => raise Interrupt 
      | _ => (print_endline x; []))
    val filel1 = List.concat (map f pbl)
    val filel2 = if b then filel1 else one_in_n 10 0 filel1
    val _ = print_endline ("evaluation: " ^ its (length filel2) ^ " problems")
    val (_,t) = add_time (parapp_queue ncore (run_evalscript dir)) filel2
  in
    print_endline ("evaluation time: " ^ rts_round 6 t)
  end

(* ------------------------------------------------------------------------
   Evaluation example runs
   ------------------------------------------------------------------------ *)

(* One example
load "tttUnfold"; open tttUnfold;
tttSetup.ttt_search_time := 5.0;
run_evalscript (tttSetup.tactictoe_dir ^ "/savestate/arithmetic170");
*)

(* One theory
load "tttUnfold"; open tttUnfold;
tttSetup.record_savestate_flag := true;
tttSetup.learn_abstract_term := true;
aiLib.debug_flag := true;
ttt_clean_record (); ttt_record_thy "arithmetic";
load "tacticToe"; open tacticToe; tactictoe ``1+1=2``;

tttSetup.ttt_search_time := 10.0;
run_evalscript_thyl "test_arithmetic-e1" false 1 ["arithmetic"];
*)

(* Core theories
load "tttUnfold"; open tttUnfold;
tttSetup.record_savestate_flag := true;
tttSetup.learn_abstract_term := false;
aiLib.debug_flag := true;
ttt_clean_record (); ttt_record ();

load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
aiLib.debug_flag := false;
tttSetup.thml_explo_flag := false;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val _ = run_evalscript_thyl "june5-16-32thms" true 30 thyl;

tttSetup.ttt_search_time := 30.0;
aiLib.debug_flag := false;
tttSetup.thml_explo_flag := true;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val _ = run_evalscript_thyl "june4-e2" true 30 thyl;
*)

(* ------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------ *)

fun listDir dirName = 
  let 
    val dir = OS.FileSys.openDir dirName
    fun read files = case OS.FileSys.readDir dir of
        NONE => rev files
      | SOME file => read (file :: files)
    val r = read []
  in
    OS.FileSys.closeDir dir; r
  end
 
fun is_proof x = (case x of Proof _ => true | _ => false)

fun extract_info dir file =
  let 
    val sl = readl (dir ^ "/" ^ file) 
    val status = 
      if exists (String.isPrefix "tactictoe: saturated") sl 
        then ProofSaturated 
      else if exists (String.isPrefix "tactictoe: timeout") sl
        then ProofTimeout
      else if exists (String.isPrefix "tactictoe: proven") sl
        then Proof "todo"
      else raise ERR "extract_info" "no status"
    val stim1 = valOf (List.find (String.isPrefix "search time:") sl)   
    val stim2 = snd (split_string "search time: " stim1)
    val t = valOf (Real.fromString stim2)
  in
    (snd (split_string "buildheap_" file), (status,t))
  end

fun write_graph file (s1,s2) l =
  writel file ((s1 ^ " " ^ s2) :: map (fn (a,b) => rts a ^ " " ^ its b) l)

fun cumul_graph timelimit exp =
  let 
    val dir = ttt_eval_dir ^ "/" ^ exp
    val filel = filter (String.isPrefix "buildheap_") (listDir dir)
    val l = map (extract_info dir) filel
    val satl = filter (fn (_,(x,_)) => x = ProofSaturated) l
    val timeoutl = filter (fn (_,(x,_)) => x = ProofSaturated) l
    val proofl = filter (fn (_,(x,_)) => is_proof x) l
    val timl = map (fn (_,(_,t)) => t) proofl
    fun f bound = length (filter (fn x => x <= bound) timl)
    val graph = map_assoc f (interval 0.1 (0.02,timelimit))
    val graph_out = ttt_eval_dir ^ "/graph/" ^ exp ^ "_graph"
    val _ = mkDir_err (ttt_eval_dir ^ "/graph")
  in
    print_endline 
      ("total: " ^ its (length l) ^ ", " ^
       "proof: " ^ its (length proofl) ^ ", " ^
       "timeout: " ^ its (length timeoutl) ^ ", " ^
       "saturated: " ^ its (length satl));
    write_graph graph_out ("time","proofs") graph
  end

(*
load "tttEval"; open tttEval;
val expl = ["june4-e1","june4-e2","june2-e1","june2-e3","june2-e4"];
app (cumul_graph 30.0) expl;
(* quit *)
gnuplot -p -e "plot 'eval/graph/june4-e1_graph' using 1:2 with lines,\
                    'eval/graph/june4-e2_graph' using 1:2 with lines,\
                    'eval/graph/june2-e1_graph' using 1:2 with lines,\
                    'eval/graph/june2-e3_graph' using 1:2 with lines,\
                    'eval/graph/june2-e4_graph' using 1:2 with lines"
*)

end (* struct *)
