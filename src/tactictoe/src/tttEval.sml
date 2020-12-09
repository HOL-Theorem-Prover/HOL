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
  mlThmData mlTacticData mlTreeNeuralNetwork
  tttSetup tttSearch tttRecord tacticToe tttTrain tttBigSteps

val ERR = mk_HOL_ERR "tttEval"

type nnfiles = string option * string option * string option

val exportfof_flag = ref false

(* -------------------------------------------------------------------------
   TNN value examples
   ------------------------------------------------------------------------- *)

fun is_proved tree = #nstatus (dfind [] tree) = NodeProved

fun export_valueex file tree =
  if not (is_proved tree) then () else 
  let
    val nodel = map snd (dlist tree)
    fun f x = (nntm_of_stateval (#goal x), 
               if #gstatus x = GoalProved then 1.0 else 0.0)
    fun g x = vector_to_list (Vector.map f (#goalv x))
    val exl = List.concat (map g nodel)
  in
    write_tnnex file (basicex_to_tnnex exl)
  end

(* -------------------------------------------------------------------------
   Exporting problems on intermediate goals
   ------------------------------------------------------------------------- *)

local open SharingTables HOLsexp in
  fun enc_tml enc_tm = list_encode enc_tm
  fun dec_tml dec_tm = list_decode dec_tm
  fun enc_tmll enc_tm = list_encode (enc_tml enc_tm)
  fun dec_tmll dec_tm = list_decode (dec_tml dec_tm)
end

fun write_pb file (gl,g) =
  let val tmll = map (fn (asl,w) => w :: asl) (g :: gl) in
    write_tmdata (enc_tmll, List.concat) file tmll
  end

fun read_pb file =
  let 
    val tmll = read_tmdata dec_tmll file
    val gl = map (fn l => (tl l, hd l)) tmll
  in
    (tl gl, hd gl)
  end

fun mk_info (id,gi,gstatus,gvis) =
  ["Path: " ^ (if null id then "top" else string_of_id id),
   "Goal: " ^ its gi,
   "Status: " ^ (if gstatus = GoalProved then "proven" else "unknown"),
   "Visits: " ^ rts gvis]

fun export_pb pbprefix (g,(id,gi,gstatus,gvis)) = 
  let 
    fun f id = if null id then "top" else string_of_id id
    val pbfile = pbprefix ^ ("-" ^ f id) ^ "-" ^ its gi
    val premises = mlNearestNeighbor.thmknn_wdep 
      (!thmdata_glob) 128 (mlFeature.fea_of_goal true g) 
    val gl = map (dest_thm o snd) (thml_of_namel premises)
  in
    write_pb pbfile (gl,g);
    writel (pbfile ^ ".info") (mk_info (id,gi,gstatus,gvis))
  end

fun export_pbl pbprefix tree =
  let
    fun f id (gi,x) = (#goal x, (id, gi, #gstatus x, #gvis x))    
    fun g (id,x) = vector_to_list (Vector.mapi (f id) (#goalv x))
    val pbl = List.concat (map g (dlist tree))
  in
    app (export_pb pbprefix) pbl
  end

(* -------------------------------------------------------------------------
   Reading the examples
   ------------------------------------------------------------------------- *)

(* 
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "aiLib"; open aiLib;
load "tttSetup"; open tttSetup;


val ERR = mk_HOL_ERR "test";
val arityd = ref (dempty String.compare)
fun sexp_tm t = 
  if is_comb t then 
    let val (oper,argl) = strip_comb t in
      arityd := dadd (fst (dest_var oper)) (length argl) (!arityd);
      "(" ^ String.concatWith " " (map sexp_tm (oper :: argl)) ^ ")"
    end
  else if is_var t then fst (dest_var t) else raise ERR "sexp_tm" "";

fun sexp_ex (t,rl) = 
  sexp_tm (rand t) ^ "\n" ^ 
  String.concatWith " " (map rts rl
writel (ttt_eval_dir ^ "/december1/sexp_value") (map sexp_ex ex);


length allex;



val tnn = train_fixed 1.0 allex;
val tnndir = ttt_eval_dir ^ "/december1/tnn";
val _ = mkDir_err tnndir;
val tnnfile = tnndir ^ "/value";
write_tnn tnnfile tnn;

load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val smlfun = "tttEval.ttt_eval";
run_evalscript_thyl smlfun "december1-gen1" (true,30) 
  (SOME tnnfile,NONE,NONE) thyl;

*)

(* -------------------------------------------------------------------------
   Evaluation function
   ------------------------------------------------------------------------- *)

fun print_status r = case r of
   ProofSaturated => print_endline "tactictoe: saturated"
 | ProofTimeout   => print_endline "tactictoe: timeout"
 | Proof s        => print_endline ("tactictoe: proven\n  " ^ s)

fun print_time (name,t) = print_endline (name ^ " time: " ^ rts_round 6 t)

fun ttt_eval expdir (thy,n) (thmdata,tacdata) nnol goal =
  let
    val valuefile = expdir ^ "/value/" ^ thy ^ "_" ^ its n
    val pbprefix = expdir ^ "/pb/" ^ thy ^ "_" ^ its n
    val mem = !hide_flag
    val _ = hide_flag := false
    val _ = print_endline ("ttt_eval: " ^ string_of_goal goal)
    val _ = print_endline ("ttt timeout: " ^ rts (!ttt_search_time))
    val ((status,tree),t) = add_time
      (main_tactictoe (thmdata,tacdata) nnol) goal
      handle Interrupt => raise Interrupt
        | e => (print_endline "Error"; raise e)
  in
    print_status status;
    print_time ("ttt_eval",t);
    print_endline ("nodes: " ^ its (dlength tree));
    print_time ("tnn value",!reward_time);
    print_time ("tnn policy",!reorder_time);
    print_time ("tactic pred",!predtac_time);
    export_valueex valuefile tree;
    if !exportfof_flag then export_pbl pbprefix tree else ();
    hide_flag := mem
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

fun assign_tnn s fileo =
  if isSome fileo
  then "val " ^ s ^ " = SOME ( mlTreeNeuralNetwork.read_tnn " ^
       mlquote (valOf fileo) ^ " );"
  else "val " ^ s ^ " = NONE : mlTreeNeuralNetwork.tnn option ;"

fun prepare_global_data (thy,n) =
  let 
    val _ = print_endline ("prepare_data: " ^ thy ^ " " ^ its n)
    val calls = mlTacticData.import_calls (ttt_tacdata_dir ^ "/" ^ thy)
    val calls_before = filter (fn ((_,x,_),_) => x < n) calls
  in
    thmdata_glob := create_thmdata ();
    tacdata_glob := foldl ttt_update_tacdata (!tacdata_glob) calls_before
  end

fun write_evalscript expdir smlfun (vnno,pnno,anno) file =
  let
    val sl = String.fields (fn x => x = #"_") (OS.Path.file file)
    val thy = String.concatWith "_" (butlast sl)
    val n = string_to_int (last sl)
    val file1 = mlquote (file ^ "_savestate")
    val file2 = mlquote (file ^ "_goal")
    val sl =
    ["PolyML.SaveState.loadState " ^ file1 ^ ";",
     "val tactictoe_goal = aiLib.import_goal " ^ file2 ^ ";",
     "load " ^ mlquote "tttEval" ^ ";",
     assign_tnn "tactictoe_vo" vnno,
     assign_tnn "tactictoe_po" pnno,
     assign_tnn "tactictoe_ao" anno,
     sreflect_real "tttSetup.ttt_search_time" ttt_search_time,
     sreflect_real "tttSetup.ttt_policy_coeff" ttt_policy_coeff,
     sreflect_real "tttSetup.ttt_explo_coeff" ttt_explo_coeff,
     sreflect_flag "aiLib.debug_flag" debug_flag,
     sreflect_flag "tttEval.exportfof_flag" exportfof_flag,
     "val _ = tttEval.prepare_global_data (" ^ 
        mlquote thy ^ "," ^ its n ^ ");",
     smlfun ^ " " ^ mlquote expdir ^ " " ^
     "(" ^ mlquote thy ^ "," ^ its n ^ ") " ^
     "(!tttRecord.thmdata_glob, !tttRecord.tacdata_glob) " ^
     "(tactictoe_vo, tactictoe_po, tactictoe_ao) " ^
     "tactictoe_goal;"]
  in
    writel (file ^ "_eval.sml") sl
  end

fun bare file = OS.Path.base (OS.Path.file file)

fun run_evalscript smlfun expdir nnol file =
  (
  write_evalscript expdir smlfun nnol file;
  run_buildheap_nodep (expdir ^ "/out") (file ^ "_eval.sml")
  )

fun run_evalscript_thyl smlfun expname (b,ncore) nnol thyl =
  let
    val savestatedir = tactictoe_dir ^ "/savestate"
    val expdir = ttt_eval_dir ^ "/" ^ expname
    val outdir = expdir ^ "/out"
    val valuedir = expdir ^ "/value"
    val tnndir = expdir ^ "/tnn"
    val pbdir = expdir ^ "/pb"
    val _ = app mkDir_err 
      [ttt_eval_dir, expdir, outdir, valuedir, pbdir, tnndir]
    val (thyl',thyl'') = partition (fn x => mem x ["min","bool"]) thyl
    val pbl = map (fn x => savestatedir ^ "/" ^ x ^ "_pbl") thyl''
    fun f x = readl x handle
        Interrupt => raise Interrupt
      | _         => (print_endline x; [])
    val filel1 = List.concat (map f pbl)
    val filel2 = if b then filel1 else one_in_n 10 0 filel1
    val _ = print_endline ("evaluation: " ^ its (length filel2) ^ " problems")
    val (_,t) = add_time
      (parapp_queue ncore (run_evalscript smlfun expdir nnol)) filel2
  in
    print_endline ("evaluation time: " ^ rts_round 6 t)
  end

(* ------------------------------------------------------------------------
   Record theory data
   ------------------------------------------------------------------------ *)

(*
load "tttUnfold"; open tttUnfold;
tttSetup.record_flag := true;
tttSetup.record_savestate_flag := false;
aiLib.load_sigobj ();
ttt_clean_record ();
ttt_record ();
*)

(* ------------------------------------------------------------------------
   Record savestates
   ------------------------------------------------------------------------ *)

(*
load "tttUnfold"; open tttUnfold;
tttSetup.record_flag := false;
tttSetup.record_savestate_flag := true;
aiLib.load_sigobj ();
ttt_record_savestate (); (* includes clean savestate *)
*)

(* ------------------------------------------------------------------------
   Evaluation on one example
   ------------------------------------------------------------------------ *)

(*
load "tttEval"; open aiLib tttSetup tttEval;
val smlfun = "tttEval.ttt_eval";
val expname = "test1";
val savestatedir = tactictoe_dir ^ "/savestate";
val expdir = ttt_eval_dir ^ "/" ^ expname;
val outdir = expdir ^ "/out"
val _ = app mkDir_err [ttt_eval_dir, expdir, outdir];
val file = savestatedir ^ "/" ^ "finite_map_170";
tttSetup.ttt_search_time := 10.0;
run_evalscript smlfun outdir (NONE,NONE,NONE) file;
*)

(* ------------------------------------------------------------------------
   Evaluation on one theory
   ------------------------------------------------------------------------ *)

(* 
load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 10.0;
run_evalscript_thyl "arithmetic_1in10" false 1 ["arithmetic"];
*)

(* ------------------------------------------------------------------------
   Evaluation on a list of theories
   ------------------------------------------------------------------------ *)

(*
load "tttUnfold"; open tttUnfold;
tttSetup.record_flag := false;
tttSetup.record_savestate_flag := true;
ttt_record_savestate ();  (* rm -r savestate if argument list is too long *)

load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val smlfun = "tttEval.ttt_eval";
exportfof_flag := true;
run_evalscript_thyl smlfun "december3-2" (true,30) (NONE,NONE,NONE) thyl;
*)

(* ------------------------------------------------------------------------
   Reinforcement learning of the value of an intermediate goal.
   ------------------------------------------------------------------------ *)

fun train_fixed pct exl =
  let
    val (train,test) = part_pct pct (shuffle exl)
    fun operl_of_tnnex exl =
      List.concat (map operl_of_term (map fst (List.concat exl)))
    val operl = operl_of_tnnex exl
    val operset = mk_fast_set (cpl_compare Term.compare Int.compare) operl
    val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operset
    val randtnn = random_tnn operdiml
    val schedule =
      [{ncore = 4, verbose = true,
       learning_rate = 0.02, batch_size = 16, nepoch = 100}];
    val tnn = train_tnn schedule randtnn (train,test)
  in
    tnn
  end

fun collect_ex dir = 
  let val filel = map (fn x => dir ^ "/" ^ x) (listDir dir) in
    List.concat (map read_tnnex filel)
  end

val ttt_eval_string = "tttEval.ttt_eval"

fun rlvalue_loop expname thyl (gen,maxgen) =
  if gen > maxgen then () else
  let 
    fun gendir x = ttt_eval_dir ^ "/" ^ expname ^ "-gen" ^ its x
    fun valuedir x = gendir x ^ "/value"    
    val dirl = List.tabulate (gen,valuedir)
    val exl = List.concat (map collect_ex dirl)
    val tnnfile = gendir (gen - 1) ^ "/tnn/value"
    val _ = if exists_file tnnfile then () (* for restarts *) else 
      write_tnn tnnfile (train_fixed 1.0 exl)
  in
    print_endline ("Generation " ^ its gen);
    run_evalscript_thyl ttt_eval_string (expname ^ "-gen" ^ its gen) (true,30) 
    (SOME tnnfile,NONE,NONE) thyl;
    rlvalue_loop expname thyl (gen+1,maxgen)
  end

fun rlvalue expname thyl maxgen =
  (
  print_endline ("Generation 0"); 
  run_evalscript_thyl ttt_eval_string (expname ^ "-gen0") (true,30) 
    (NONE,NONE,NONE) thyl;
  rlvalue_loop expname thyl (1,maxgen)
  )

(* training test 
load "tttEval"; open tttEval mlTreeNeuralNetwork aiLib;


val ttt_eval_dir = HOLDIR ^ "/src/tactictoe/eval";
val valuedir = ttt_eval_dir ^ "/december5-gen0/value";

fun collect_ex dir = 
  let val filel = map (fn x => dir ^ "/" ^ x) (listDir dir) in
    List.concat (map read_tnnex filel)
  end

val exl = collect_ex valuedir;
stats_tnnex exl;
val (_,t) = add_time prepare_tnnex exl;

fun operl_of_tnnex exl =
   List.concat (map operl_of_term (map fst (List.concat exl)));
val operl = operl_of_tnnex exl;
val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operl;

fun train_fixed schedule exl =
  let
    val (train,test) = part_pct 1.0 (shuffle exl)
    fun operl_of_tnnex exl =
      List.concat (map operl_of_term (map fst (List.concat exl)))
    val operl = operl_of_tnnex exl
    val operset = mk_fast_set (cpl_compare Term.compare Int.compare) operl
    val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operset
    val randtnn = random_tnn operdiml
   
    val tnn = train_tnn schedule randtnn (train,test)
  in
    tnn
  end

val schedule =
    [{ncore = 4, verbose = true,
     learning_rate = 0.02, batch_size = 16, nepoch = 1}];

val tnn = train_fixed schedule exl;


*)


(*
load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
val expname = "december5";
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val maxgen = 2;
rlvalue expname thyl maxgen;
rlvalue_loop expname thyl (1,maxgen);
*)



(* ------------------------------------------------------------------------
   Bigsteps / learning / bigsteps
   ------------------------------------------------------------------------ *)

(*
load "tttUnfold"; open tttUnfold;
tttSetup.record_savestate_flag := true;
tttSetup.learn_abstract_term := false;
aiLib.debug_flag := false;
ttt_clean_record ();
ttt_record ();


load "tttEval"; open tttEval;
open mlTreeNeuralNetwork aiLib tttTrain tttEval;

tttSetup.ttt_search_time := 30.0;
aiLib.debug_flag := false;
val thyl = sort_thyl (ancestry (current_theory ()));

val expname = "october11";
val expdir = tttSetup.ttt_eval_dir ^ "/" ^ expname;
val gendir = expdir ^ "/" ^ aiLib.its 0;
val valdir = gendir ^ "/val";
val poldir = gendir ^ "/pol";
val argdir = gendir ^ "/arg";
fun prefix s = SOME (gendir ^ "/tnn" ^ s);
val (vnno,pnno,anno) = triple_of_list (map prefix ["val","pol","arg"]);

fun read_ex dir =
  let val filel = map (fn x => dir ^ "/" ^ x) (listDir dir) in
    List.concat (map read_tnnex filel)
  end;

val smlfun0 = "tttBigSteps.run_bigsteps_eval (" ^
  mlquote expdir ^ "," ^ its 0 ^ ")";
val smlfun1 = "tttBigSteps.run_bigsteps_eval (" ^
  mlquote expdir ^ "," ^ its 1 ^ ")";

fun train_dir limit dir name =
  let
    val ex1 = read_ex dir
    val _ = print_endline (its (length ex1))
    val ex2 = filter (fn x => term_size (fst (hd x)) < limit) ex1
    val _ = print_endline (its (length ex2))
    val tnn = train_fixed 0.95 ex2
  in
    write_tnn (gendir ^ "/" ^ name) tnn
  end;

val _ = run_evalscript_thyl smlfun0 expname (true,30) (NONE,NONE,NONE) thyl;
val _ = train_dir 40 valdir "tnnval";
val _ = train_dir 60 poldir "tnnpol";
val _ = train_dir 100 argdir "tnnarg";
val _ = run_evalscript_thyl smlfun1 expname (true,30) (vnno,pnno,anno) thyl;

*)

(* ------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------ *)

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
val expl = ["august11-300","august10"];
app (cumul_graph 300.0) expl;
(* quit *)
gnuplot -p -e "plot 'eval/graph/august10_graph' using 1:2 with lines,\
                    'eval/graph/august11-300_graph' using 1:2 with lines"
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
compare_stats ["august9"] "august10";
*)



end (* struct *)
