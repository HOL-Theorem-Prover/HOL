(* ========================================================================= *)
(* FILE          : tttEval.sml                                               *)
(* DESCRIPTION   : Evaluation framework for TacticToe                        *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttEval :> tttEval =
struct

open HolKernel Abbrev boolLib aiLib 
  smlRedirect smlParallel smlOpen 
  mlTacticData mlTreeNeuralNetwork
  tttSetup tttSearch tttRecord tacticToe

val ERR = mk_HOL_ERR "tttEval"

(* -------------------------------------------------------------------------
   Extracting examples from search tree
   ------------------------------------------------------------------------- *)

fun extract_exl tree =
  let 
    val nodel = map snd (dlist tree)
    fun get_gl node = (vector_to_list o Vector.map #goal o #goalv) node
    fun is_win node = #nodestatus node = NodeProved
  in
    map (fn x => (get_gl x, is_win x)) nodel
  end

(* -------------------------------------------------------------------------
   Evaluation function
   ------------------------------------------------------------------------- *)

fun print_status r = case r of
   ProofSaturated => print_endline "tactictoe: saturated"
 | ProofTimeout   => print_endline "tactictoe: timeout"
 | Proof s        => print_endline ("tactictoe: proven\n  " ^ s)

fun ttt_eval ((thmdata,tacdata),tnno) goal =
  let
    val thmid = current_theory () ^ "_" ^ its (!savestate_level - 1)
    val b = !hide_flag
    val _ = hide_flag := false
    val _ = print_endline ("ttt_eval: " ^ string_of_goal goal)
    val _ = print_endline ("ttt timeout: " ^ rts (!ttt_search_time))
    val ((status,tree),t) = add_time 
      (main_tactictoe ((thmdata,tacdata),tnno)) goal
    val _ = if not (isSome tnno) then (* only one loop for now *)
      (case status of Proof _ => 
        ttt_export_exl thmid (extract_exl tree)
      | _ => ())
      else ()
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
   - avoid using MLTON during configuration?
   ------------------------------------------------------------------------ *)

fun sreflect_real s r = ("val _ = " ^ s ^ " := " ^ rts (!r) ^ ";")
fun sreflect_flag s flag = ("val _ = " ^ s ^ " := " ^ bts (!flag) ^ ";")

fun write_evalscript tnno file =
  let
    val file1 = mlquote (file ^ "_savestate")
    val file2 = mlquote (file ^ "_goal")
    val tnndir = HOLDIR ^ "/src/tactictoe/tnn"
    val file3o = Option.map (fn x => tnndir ^ "/" ^ x) tnno
    val sl =
    ["PolyML.SaveState.loadState " ^ file1 ^ ";",
     "val tactictoe_goal = mlTacticData.import_goal " ^ file2 ^ ";",
     "load " ^ mlquote "tttEval" ^ ";",
     if isSome tnno 
     then "val tactictoe_tnno = SOME (mlTreeNeuralNetwork.read_tnn " ^ 
       mlquote (valOf file3o) ^ ");"
     else "val tactictoe_tnno = NONE : mlTreeNeuralNetwork.tnn option ;",
     sreflect_real "tttSetup.ttt_search_time" ttt_search_time,
     sreflect_real "tttSetup.ttt_policy_coeff" ttt_policy_coeff,
     sreflect_real "tttSetup.ttt_explo_coeff" ttt_explo_coeff,
     sreflect_flag "tttSetup.thml_explo_flag" thml_explo_flag,
     sreflect_flag "aiLib.debug_flag" debug_flag,
     "tttEval.ttt_eval " ^
     "((!tttRecord.thmdata_glob, !tttRecord.tacdata_glob), tactictoe_tnno) " ^
     "tactictoe_goal;"]
  in
    writel (file ^ "_eval.sml") sl
  end

fun bare file = OS.Path.base (OS.Path.file file)

fun run_evalscript dir tnno file =
  (
  write_evalscript tnno file;
  run_buildheap_nodep dir (file ^ "_eval.sml")
  )

fun run_evalscript_thyl expname (b,tnno,ncore) thyl =
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
    val (_,t) = add_time (parapp_queue ncore (run_evalscript dir tnno)) filel2
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
tttSetup.learn_abstract_term := false;
aiLib.debug_flag := true;
ttt_clean_record (); ttt_record_thy "arithmetic";
load "tacticToe"; open tacticToe; tactictoe ``1+1=2``;

tttSetup.ttt_search_time := 10.0;
run_evalscript_thyl "test_arithmetic-e1" false 1 ["arithmetic"];
*)

(* Core theories
sshload "tttUnfold"; open tttUnfold;
tttSetup.record_savestate_flag := true;
tttSetup.learn_abstract_term := false;
aiLib.debug_flag := false;
ttt_clean_record (); ttt_record ();

load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
aiLib.debug_flag := false;
tttSetup.thml_explo_flag := false;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));

val _ = run_evalscript_thyl "june15" (true,NONE,30) thyl;
val tnn = train_value 0.95 "value";
val _ = run_evalscript_thyl "june15_tnn" (true,SOME "value",30) thyl;
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

fun stats_exp exp =
  let   
    val dir = ttt_eval_dir ^ "/" ^ exp
    val filel = filter (String.isPrefix "buildheap_") (listDir dir)
    val totl = map (extract_info dir) filel
    val satl = filter (fn (_,(x,_)) => x = ProofSaturated) totl
    val timeoutl = filter (fn (_,(x,_)) => x = ProofSaturated) totl
    val proofl = filter (fn (_,(x,_)) => is_proof x) totl
  in
    (totl,satl,timeoutl,proofl)
  end

fun cumul_graph timelimit exp =
  let 
    val (l,satl,timeoutl,proofl) = stats_exp exp
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

fun compare_stats expl exp = 
  let 
    val dproven = ref (HOLset.empty String.compare)
    val dtot = ref (HOLset.empty String.compare)
    fun f (totl,_,_,proofl) = 
      let 
        val sl1 = map fst proofl 
        val sl2 = map fst totl
      in
        dproven := HOLset.addList (!dproven,sl1);
        dtot := HOLset.addList (!dtot,sl2)
      end
    val _ = app f (map stats_exp expl)
    val lproven1 = (!dproven)
    val ltot1 = (!dtot)
    val _ = f (stats_exp exp)
    val lproven2 = (!dproven)
    val ltot2 = (!dtot)
    val uniq = HOLset.difference (lproven2,lproven1)
    fun g (name,set) = print_endline (name ^ ": " ^ its (HOLset.numItems set))
  in
    app g [("total (old)",ltot1),("proven (old)",lproven1),
           ("total (new)",ltot2),("proven (new)",lproven2),
           ("unique: ", uniq)];
    print_endline ("\n  " ^ String.concatWith "\n  " (HOLset.listItems uniq))
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

(* ------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------ *)

fun train_value pct file =
  let
    val filel = listDir (HOLDIR ^ "/src/tactictoe/gl_value")
    val exll = map (fn x => ttt_import_exl x handle Interrupt => raise 
      Interrupt | _ => (print_endline x; [])) filel;
    fun f (gl,b) = (nntm_of_gl gl, if b then [1.0] else [0.0])
    val exl = map (single o f) (List.concat exll)
    val (train,test) = part_pct pct (shuffle exl)
    val operl = mk_fast_set oper_compare
      (List.concat (map operl_of_term (map fst (List.concat exl))))
    val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operl
    val randtnn = random_tnn operdiml
    val schedule =
      [{ncore = 4, verbose = true,
       learning_rate = 0.02, batch_size = 16, nepoch = 100}];
    val tnn = train_tnn schedule randtnn (train,test)
    val tnndir = HOLDIR ^ "/src/tactictoe/tnn"
    val acctrain = tnn_accuracy tnn train
    val acctest = tnn_accuracy tnn test 
  in
    print_endline ("train accuracy: " ^ rts_round 6 acctrain ^ 
      ", test accuracy: " ^ rts_round 6 acctest);
    mkDir_err tnndir;
    write_tnn (tnndir ^ "/" ^ file) tnn;
    tnn
  end

(*
load "tttEval"; open tttEval;
val tnn = train_value "value";
*)

end (* struct *)
