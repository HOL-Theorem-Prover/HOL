(* ========================================================================= *)
(* FILE          : tttEval.sml                                               *)
(* DESCRIPTION   : Evaluation framework for TacticToe                        *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttEval :> tttEval =
struct

open HolKernel Abbrev boolLib aiLib 
  smlRedirect smlParallel smlOpen smlParser 
  mlTacticData mlTreeNeuralNetwork
  tttSetup tttSearch tttRecord tacticToe

val ERR = mk_HOL_ERR "tttEval"

type pvfiles = string option * string option
val tnnex_dir = tactictoe_dir ^ "/tnnex" 
val tnn_dir = tactictoe_dir ^ "/tnn" 

(* -------------------------------------------------------------------------
   Value examples
   ------------------------------------------------------------------------- *)

fun extract_value tree =
  let 
    val nodel = map snd (dlist tree)
    fun get_valuetm node = 
      (nntm_of_gl o vector_to_list o Vector.map #goal o #goalv) node
    fun is_win node = case #nodestatus node of NodeProved => 1.0 | _ => 0.0
  in
    basicex_to_tnnex (map (fn x => (get_valuetm x, is_win x)) nodel)
  end

(*
(* -------------------------------------------------------------------------
   Policy examples
   ------------------------------------------------------------------------- *)

fun btr b = if b then 1.0 else 0.0

fun extract_policy tree =
  let 
    val nodel = map snd (dlist tree)
    val goalrecl1 = List.concat (map (vector_to_list o #goalv) nodel)
    val goalrecl2 = filter (fn x => #goalstatus x = GoalProved) goalrecl1
    fun f x = distrib [(#goal x, number_snd 0 (vector_to_list (#stacv x)))]
    val stacrecl = List.concat (map f goalrecl2)
    fun is_win x = case #stacstatus x of StacProved => true | _ => false
    fun not_fresh x = case #stacstatus x of StacFresh => false | _ => true
    fun g (goal,(stacv,stacn)) = 
      if is_win stacv orelse (stacn < 10 andalso not_fresh stacv)
      then SOME (nntm_of_gstactm (goal, #stactm stacv), btr (is_win stacv))
      else NONE
  in
    List.mapPartial g stacrecl
  end

(* -------------------------------------------------------------------------
   Policy examples
   ------------------------------------------------------------------------- *)

fun extract_thmpol tree =
  let 
    val nodel = map snd (dlist tree)
    val goalrecl1 = List.concat (map (vector_to_list o #goalv) nodel)
    val goalrecl2 = filter (fn x => #goalstatus x = GoalProved) goalrecl1
    fun f x = distrib [(#goal x, number_snd 0 (vector_to_list (#stacv x)))]
    val stacrecl = List.concat (map f goalrecl2)
    fun is_win x = case #stacstatus x of StacProved => true | _ => false
    fun not_fresh x = case #stacstatus x of StacFresh => false | _ => true
    fun g (goal,(stacv,stacn)) = 
      if is_win stacv andalso is_thmlarg_stac (#astac stacv)
      then SOME (nntm_of_gstactm (goal, #stactm stacv), btr (is_win stacv))
      else NONE
    val thml = 

  in
    List.mapPartial g stacrecl
  end


fun thml_of_sml sthml_of_thmidl

fun minimize

fun minimize astac sthml
  let 
    val x = drop_sig thmlarg_placeholder
    val astac' = replace_string (thmlarg_placeholder) x astac
    fun f = thmlstac_of_sml ("fn " ^ x ^ " => (" ^ astac ^ ")")     
    val thml = combine (thml_of_sml sthml, sthml)
      handle Interrupt => raise Interrupt | _ => 
        (print_endline "error: minimize: parsing theorems"; [])
  in
    minimize f thml

let val thml =
  

(* results should be (tm,1.0) or (tm,0.0) where tm in the encoding of
a theorem *)
*)
(* -------------------------------------------------------------------------
   Evaluation function
   ------------------------------------------------------------------------- *)

fun print_status r = case r of
   ProofSaturated => print_endline "tactictoe: saturated"
 | ProofTimeout   => print_endline "tactictoe: timeout"
 | Proof s        => print_endline ("tactictoe: proven\n  " ^ s)

fun print_time (name,t) = print_endline (name ^ " time: " ^ rts_round 6 t)

fun ttt_clean_eval () = clean_rec_dir (tactictoe_dir ^ "/tnnex")

(* TODO: tnnex as S-expression *)
fun ttt_eval (thmdata,tacdata) (vnno,pnno) goal =
  let
    val thmid = current_theory () ^ "_" ^ its (!savestate_level - 1)
    val b = !hide_flag
    val _ = hide_flag := false
    
    val _ = mkDir_err tnnex_dir
    val value_dir = tnnex_dir ^ "/value"
    val policy_dir = tnnex_dir ^ "/policy"
    val thmpol_dir = tnnex_dir ^ "/thmpol"
    val _ = app mkDir_err [value_dir,policy_dir,thmpol_dir];
    val _ = print_endline ("ttt_eval: " ^ string_of_goal goal)
    val _ = print_endline ("ttt timeout: " ^ rts (!ttt_search_time))
    val ((status,tree),t) = add_time 
      (main_tactictoe (thmdata,tacdata) (vnno,pnno)) goal
    val _ = if not (isSome vnno) andalso not (isSome pnno) then
      (case status of Proof _ => 
        (
        write_tnnex (value_dir ^ "/" ^ thmid) (extract_value tree)
       (* write_tnnex (policy_dir ^ "/" ^ thmid) (extract_policy tree);
        write_tnnex (thmpol_dir ^ "/" ^ thmid) (extract_thmpol tree) *)
        )
      | _ => ())
      else ()
  in   
    print_status status;
    print_time ("ttt_eval",t);
    print_time ("tnn value",!reward_time);
    print_time ("tnn policy",!reorder_time);
    print_time ("tactic pred",!tacpred_time);
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

fun write_evalscript (vnno,pnno) file =
  let
    val file1 = mlquote (file ^ "_savestate")
    val file2 = mlquote (file ^ "_goal")
    val filevo = Option.map (fn x => tnn_dir ^ "/" ^ x) vnno
    val filepo = Option.map (fn x => tnn_dir ^ "/" ^ x) pnno
    val sl =
    ["PolyML.SaveState.loadState " ^ file1 ^ ";",
     "val tactictoe_goal = mlTacticData.import_goal " ^ file2 ^ ";",
     "load " ^ mlquote "tttEval" ^ ";",
     if isSome filevo
     then "val tactictoe_vnno = SOME (mlTreeNeuralNetwork.read_tnn " ^ 
       mlquote (valOf filevo) ^ ");"
     else "val tactictoe_vnno = NONE : mlTreeNeuralNetwork.tnn option ;",
     if isSome filepo
     then "val tactictoe_pnno = SOME (mlTreeNeuralNetwork.read_tnn " ^ 
       mlquote (valOf filepo) ^ ");"
     else "val tactictoe_pnno = NONE : mlTreeNeuralNetwork.tnn option ;",
     sreflect_real "tttSetup.ttt_search_time" ttt_search_time,
     sreflect_real "tttSetup.ttt_policy_coeff" ttt_policy_coeff,
     sreflect_real "tttSetup.ttt_explo_coeff" ttt_explo_coeff,
     sreflect_flag "tttSetup.thml_explo_flag" thml_explo_flag,
     sreflect_flag "aiLib.debug_flag" debug_flag,
     "tttEval.ttt_eval " ^
     "(!tttRecord.thmdata_glob, !tttRecord.tacdata_glob) " ^
     "(tactictoe_vnno, tactictoe_pnno) " ^
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

fun run_evalscript_thyl expname (b,ncore) tnno thyl =
  let
    val dir = ttt_eval_dir ^ "/" ^ expname ^ 
      (if b then "" else "_tenth")
    val _ = (mkDir_err ttt_eval_dir; mkDir_err dir)
    val thyl' = filter (fn x => not (mem x ["min","bool"])) thyl
    val pbl = map (fn x => tactictoe_dir ^ "/savestate/" ^ x ^ "_pbl") thyl'
    fun f x = (readl x handle Interrupt => raise Interrupt 
      | _ => (print_endline x; []))
    val filel1 = List.concat (map f pbl)
    val filel2 = if b then filel1 else one_in_n 10 0 filel1
    val _ = print_endline ("evaluation: " ^ its (length filel2) ^ " problems")
    val (_,t) = add_time 
      (parapp_queue ncore (run_evalscript dir tnno)) filel2
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
load "tttUnfold"; open tttUnfold;
tttSetup.record_savestate_flag := true;
tttSetup.learn_abstract_term := false;
aiLib.debug_flag := false;
ttt_clean_record (); ttt_record ();

load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
aiLib.debug_flag := false;
tttSetup.thml_explo_flag := false;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));

val _ = ttt_clean_eval ();
val _ = run_evalscript_thyl "july13" (true,30) (NONE,NONE) thyl;
val tnn_value = train_value 0.95 "value";
val tnn_policy = train_policy 0.95 "policy";
val _ = run_evalscript_thyl "june23_tnn" (true,30) (SOME "value", SOME "policy") thyl;
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
compare_stats ["june15"] "june15_tnn";
*)

(* ------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------ *)

fun operl_of_tnnex exl =
  List.concat (map operl_of_term (map fst (List.concat exl)))

fun train_dir pct name =
  let
    val filel = listDir (tactictoe_dir ^ "/tnnex/" ^ name)
    val exl = List.concat (map read_tnnex filel)
    val (train,test) = part_pct pct (shuffle exl)
    val operl = operl_of_tnnex exl
    val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operl
    val randtnn = random_tnn operdiml
    val schedule =
      [{ncore = 4, verbose = true,
       learning_rate = 0.02, batch_size = 16, nepoch = 100}];
    val tnn = train_tnn schedule randtnn (train,test)
    val acctrain = tnn_accuracy tnn train
    val acctest = tnn_accuracy tnn test 
  in
    print_endline ("train accuracy: " ^ rts_round 6 acctrain ^ 
      ", test accuracy: " ^ rts_round 6 acctest);
    mkDir_err tnn_dir;
    write_tnn (tnn_dir ^ "/" ^ name) tnn;
    tnn
  end
 
fun train_value pct file = train_dir pct "value"
fun train_policy pct file = train_dir pct "policy"
fun train_thmpol pct file = train_dir pct "thmpol"


end (* struct *)
