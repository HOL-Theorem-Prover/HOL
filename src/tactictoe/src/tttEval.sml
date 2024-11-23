(* ========================================================================= *)
(* FILE          : tttEval.sml                                               *)
(* DESCRIPTION   : Evaluation framework for TacticToe                        *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttEval :> tttEval =
struct

open HolKernel Abbrev boolLib aiLib
  smlRedirect smlParallel smlOpen smlParser smlExecute
  mlThmData mlTacticData mlTreeNeuralNetwork
  tttSetup tttSearch tttRecord tacticToe tttToken tttTrain

val ERR = mk_HOL_ERR "tttEval"
fun catch_err msg f x =
  f x handle HOL_ERR {origin_structure,origin_function,source_location,message} =>
  (print_endline
    (msg ^ ":" ^ origin_structure ^ ":" ^ origin_function ^ ":" ^ locn.toShortString source_location ^ ":" ^ message);
  raise ERR "tttEval" "error caught (see log)")
fun catch_err_ignore msg f x =
  f x handle HOL_ERR {origin_structure,origin_function,source_location,message} =>
  (print_endline
    (msg ^ ":" ^ origin_structure ^ ":" ^ origin_function ^ ":" ^ locn.toShortString source_location ^ ":" ^ message))


(* -------------------------------------------------------------------------
   Import holyhammer if possible
   ------------------------------------------------------------------------- *)

val hh_glob = ref NONE
val hh_timeout = ref 30

fun metis_avail () = quse_string "val _ = metisTools.METIS_TAC;"

fun import_hh () =
  let val _ =
     metis_avail () andalso
     quse_string ("load \"holyHammer\"; " ^
                  "holyHammer.set_timeout " ^ its (!hh_timeout) ^ ";" ^
                  "tttEval.hh_glob := Option.SOME (holyHammer.main_hh);")
  in
    !hh_glob
  end

(* -------------------------------------------------------------------------
   I/O
   ------------------------------------------------------------------------- *)

type nnfiles = string option * string option * string option

(* --------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------ *)

fun is_proof x = (case x of Proof _ => true | _ => false)

val keyl = ["nodes:","loops:",
  "search:","select:","exparg:","apply:","backup:","recons:",
  "metis:","other:","tactictoe:"]

fun parse_info file l =
  let val msg = file ^ " -- " ^ String.concatWith " " (map fst l) in
    if length l <> length keyl then raise ERR "parse_info" msg else
    let
      fun parse_int s (s1,s2) =
        if s = s1 then string_to_int s2 else
          raise ERR "parse_int" (msg ^ " -- " ^ s)
      fun parse_real s (s1,s2) =
        if s = s1 then valOf (Real.fromString s2) else
          raise ERR "parse_real" (msg ^ " -- " ^ s)
      fun parse_status s (s1,s2) =
        if s = s1 then s2 else
          raise ERR "parse_status" (msg ^ " -- " ^ s)
    in
      {
      loops = parse_int "loops:" (List.nth (l,0)),
      nodes = parse_int "nodes:" (List.nth (l,1)),
      search = parse_real "search:" (List.nth (l,2)),
      select = parse_real "select:" (List.nth (l,3)),
      exparg = parse_real "exparg:" (List.nth (l,4)),
      apply = parse_real "apply:" (List.nth (l,5)),
      backup = parse_real "backup:" (List.nth (l,6)),
      recons = parse_real "recons:" (List.nth (l,7)),
      metis = parse_real "metis:" (List.nth (l,8)),
      other = parse_real "other:" (List.nth (l,9)),
      status = parse_status "tactictoe:" (List.nth (l,10))
      }
    end
  end

fun all_info dir file =
  let
    val sl = readl (dir ^ "/" ^ file)
    fun read_line line = case String.tokens Char.isSpace line of
       [a,b] => if mem a keyl then SOME (a,b) else NONE
     | _ => NONE
  in
    parse_info file (List.mapPartial read_line sl)
  end

fun compile_info exp =
  let
    val dir = ttt_eval_dir ^ "/" ^ exp ^ "/out"
    val filel = filter (String.isPrefix "buildheap_") (listDir dir)
    val statsl = map (all_info dir) filel
    val provenl = filter (fn x => #status x = "proven") statsl
    val timeoutl = filter (fn x => #status x = "timeout") statsl
    val saturatedl = filter (fn x => #status x = "saturated") statsl
    val totsearch = sum_real (map #search statsl)
    val totnodes = Real.fromInt (sum_int (map #nodes statsl))
    val totloops = Real.fromInt (sum_int (map #loops statsl))
  in
    String.concatWith "\n" [
    "total " ^ its (length statsl),
    "proven " ^ its (length provenl),
    "timeout " ^ its (length timeoutl),
    "saturated " ^ its (length saturatedl),
    "nodes_per_sec " ^ rts_round 2 (totnodes / totsearch),
    "loops_per_sec " ^ rts_round 2 (totloops / totsearch),
    "select " ^ rts_round 6 (sum_real (map #select statsl) / totsearch),
    "exparg " ^ rts_round 6 (sum_real (map #exparg statsl) / totsearch),
    "apply " ^ rts_round 6 (sum_real (map #apply statsl) / totsearch),
    "backup " ^ rts_round 6 (sum_real (map #backup statsl) / totsearch),
    "recons_average " ^ rts_round 6 (sum_real (map #recons statsl) /
       Real.fromInt (length provenl)),
    "metis " ^ rts_round 6 (sum_real (map #metis statsl) / totsearch),
    "other " ^ rts_round 6 (sum_real (map #other statsl) / totsearch)]
  end

(* load "tttEval"; open tttEval aiLib;
   print_endline (compile_info "reimp1-gen0"); *)

fun extract_info dir file =
  let
    val _ = print_endline file
    val sl = readl (dir ^ "/" ^ file)
    val status =
      if exists (String.isPrefix "tactictoe: saturated") sl
        then ProofSaturated
      else if exists (String.isPrefix "tactictoe: timeout") sl
        then ProofTimeout
      else if exists (String.isPrefix "tactictoe: proven") sl
        then Proof "todo"
      else raise ERR "extract_info" "no status"
    val stim1 = valOf (List.find (String.isPrefix "search: ") sl)
    val stim2 = snd (split_string "search: " stim1)
    val t = valOf (Real.fromString stim2)
  in
    (snd (split_string "buildheap_" file), status, t)
  end

fun write_graph file (s1,s2) l =
  writel file ((s1 ^ " " ^ s2) :: map (fn (a,b) => rts a ^ " " ^ its b) l)

fun proofl_exp exp =
  let
    val dir = ttt_eval_dir ^ "/" ^ exp ^ "/out"
    val filel = filter (String.isPrefix "buildheap_") (listDir dir)
    val totl = map (extract_info dir) filel
    val proofl = filter (fn (_,x,_) => is_proof x) totl
  in
    map (fn (a,_,b) => (a,b)) proofl
  end

(*
load "tttEval"; open tttEval;
load "aiLib"; open aiLib;
val l1 = proofl_exp "rl-full-gen0";
val d1 = dnew String.compare l1;
val l2 = proofl_exp "rl-full-gen1";
val d2 = dnew String.compare l2;

val l2nl1 = filter (fn (x,_) => not (dmem x d1)) l2;
length l2nl1;

val l1nl2 = filter (fn (x,_) => not (dmem x d2)) l1;
length l1nl2;

val l2nl1s = dict_sort compare_rmin l2nl1;

val topol = filter (fn (x,_) => String.isPrefix "real_topology" x) l2nl1s;

*)




(* -------------------------------------------------------------------------
   TNN value examples
   ------------------------------------------------------------------------- *)

fun allgoalrec_searchtree tree = case tree of
  SearchNode (_,gtreev) =>
    vector_to_list (Vector.map get_stacrecord gtreev) @
    List.concat (vector_to_list (Vector.map allgoalrec_stactree gtreev))
and allgoalrec_stactree stactree = case stactree of
    StacNode (_,svo) => (case svo of NONE => [] | SOME (sv,sl) =>
      List.concat (vector_to_list (Vector.map allgoalrec_stactree sv)))
  | StacLeaf (_,NONE) => []
  | StacLeaf (_,SOME ctree) => allgoalrec_searchtree ctree


fun export_valex file (tree as SearchNode (r,gtreev)) =
  if #nstatus r = Proved then () else
  let
    val goalrecl = allgoalrec_searchtree tree
    fun f x = ((nntm_of_stateval (dest_goal (#gtoken x)),
               if #sstatus x = Proved then 1.0 else 0.0), #svis x)
    val exl1 = map f goalrecl
    val exl2 = filter (fn ((t,_),_) => term_size t < 80) exl1
    val (posl,negl) = partition (fn x => snd (fst x) > 0.5) exl2
    val posl2 = first_n 600 (dict_sort compare_rmax posl)
    val negl2 = first_n 600 (dict_sort compare_rmax negl)
  in
    write_tnnex file (basicex_to_tnnex (map fst (posl2 @ negl2)))
  end

(* -------------------------------------------------------------------------
   Evaluation function
   ------------------------------------------------------------------------- *)

fun print_status r = case r of
   ProofSaturated => print_endline "tactictoe: saturated"
 | ProofTimeout   => print_endline "tactictoe: timeout"
 | Proof s        => print_endline ("tactictoe: proven\n  " ^ s)

val hh_flag = ref false

fun hh_call fofdir thmdata goal =
  let val hho = import_hh () in
  if not (isSome hho) then print_endline "hh: not available" else
  let
    val hh = valOf hho
    fun hh_err x y z = ignore (hh x y z)
    val (_,t) = add_time (hh_err fofdir thmdata) goal
  in
    print_endline ("hh_eval: " ^ rts_round 6 t)
  end end

fun ttt_eval expdir (thy,n) (thmdata,tacdata) nnol goal =
  let
    val pbid = thy ^ "_" ^ its n
    val valfile = expdir ^ "/val/" ^ pbid
    val argfile = expdir ^ "/arg/" ^ pbid
    val pbprefix = expdir ^ "/pb/" ^ pbid
    val fofdir = expdir ^ "/fof/" ^ pbid
    val _ = atp_dir := fofdir
    val _ = app mkDir_err [expdir ^ "/fof", fofdir]
    val mem = !hide_flag
    val _ = hide_flag := false
    val _ = print_endline ("ttt_eval: " ^ string_of_goal goal)
    val _ = print_endline ("ttt timeout: " ^ rts (!ttt_search_time))
  in
    if !hh_flag
      then catch_err_ignore "hh_call" (hh_call fofdir thmdata) goal else
    let val ((status,tree),t) = add_time
      (main_tactictoe (thmdata,tacdata) nnol) goal
      handle Interrupt => raise Interrupt
        | e => (print_endline "Error"; raise e)
    in
      print_status status;
      print_endline ("ttt_eval: " ^ rts_round 6 t);
      export_valex valfile tree
    end
    ;
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
fun sreflect_int s r = ("val _ = " ^ s ^ " := " ^ its (!r) ^ ";")
fun sreflect_flag s flag = ("val _ = " ^ s ^ " := " ^ bts (!flag) ^ ";")

fun assign_tnn s fileo =
  if isSome fileo
  then "val " ^ s ^ " = SOME ( mlTreeNeuralNetwork.read_tnn " ^
       mlquote (valOf fileo) ^ " );"
  else "val " ^ s ^ " = NONE : mlTreeNeuralNetwork.tnn option ;"

val cheat_flag = ref false

fun prepare_global_data (thy,n) =
  let
    val _ = print_endline ("prepare_data: " ^ thy ^ " " ^ its n)
    val calls = mlTacticData.import_calls (ttt_tacdata_dir ^ "/" ^ thy)
    val m = if !cheat_flag then n + 1 else n
    val calls_before = filter (fn ((_,x,_),_) => x < m) calls
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
     sreflect_flag "tttSetup.ttt_metis_flag" ttt_metis_flag,
     sreflect_flag "aiLib.debug_flag" debug_flag,
     sreflect_flag "tttEval.cheat_flag" cheat_flag,
     sreflect_flag "tttEval.hh_flag" hh_flag,
     sreflect_int "tttEval.hh_timeout" hh_timeout,
     sreflect_flag "tacticToe.hh_use" hh_use,
     sreflect_int "tacticToe.hh_time" hh_time,
     sreflect_flag "tttSearch.conttop_flag" conttop_flag,
     sreflect_flag "tttSearch.contmid_flag" contmid_flag,
     sreflect_real "tttSearch.default_reward" default_reward,
     "val _ = tttEval.prepare_global_data (" ^
        mlquote thy ^ "," ^ its n ^ ");",
     sreflect_flag "tttSearch.nocut_flag" nocut_flag,
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
  (write_evalscript expdir smlfun nnol file;
   smlExecScripts.exec_ttteval (expdir ^ "/out") (file ^ "_eval.sml"))

val savestatedir = tactictoe_dir ^ "/savestate"

val oldeval_flag = ref false
fun is_oldeval file = readl (file ^ "_flags") = ["false","false"]

fun run_evalscript_thyl smlfun expname (b,ncore) nnol thyl =
  let
    val expdir = ttt_eval_dir ^ "/" ^ expname
    val outdir = expdir ^ "/out"
    val valdir = expdir ^ "/val"
    val argdir = expdir ^ "/arg"
    val tnndir = expdir ^ "/tnn"
    val pbdir = expdir ^ "/pb"
    val _ = app mkDir_err
      [ttt_eval_dir, expdir, outdir, valdir, argdir, pbdir, tnndir]
    val (thyl',thyl'') = partition (fn x => mem x ["min","bool"]) thyl
    val pbl = map (fn x => savestatedir ^ "/" ^ x ^ "_pbl") thyl''
    fun f x = readl x handle
        Interrupt => raise Interrupt
      | _         => (print_endline x; [])
    val filel1 = List.concat (map f pbl)
    val filel2 = if b then filel1 else one_in_n 10 0 filel1
    val filel3 = if !oldeval_flag then filter is_oldeval filel2 else filel2
    val _ = print_endline ("evaluation: " ^ its (length filel3) ^ " problems")
    val (_,t) = add_time
      (parapp_queue ncore (run_evalscript smlfun expdir nnol)) filel3
    val infos =
      ("evaluation time: " ^ rts_round 6 t) ^ "\n" ^ compile_info expname
  in
    (print_endline infos; writel (expdir ^ "/stats") [infos])
  end

fun run_evalscript_filel smlfun expname (b,ncore) nnol filel =
  let
    val savestatedir = tactictoe_dir ^ "/savestate"
    val expdir = ttt_eval_dir ^ "/" ^ expname
    val outdir = expdir ^ "/out"
    val valdir = expdir ^ "/val"
    val argdir = expdir ^ "/arg"
    val tnndir = expdir ^ "/tnn"
    val pbdir = expdir ^ "/pb"
    val _ = app mkDir_err
      [ttt_eval_dir, expdir, outdir, valdir, argdir, pbdir, tnndir]
    val _ = print_endline ("evaluation: " ^ its (length filel) ^ " problems")
    val (_,t) = add_time
      (parapp_queue ncore (run_evalscript smlfun expdir nnol)) filel
    val infos =
      ("evaluation time: " ^ rts_round 6 t) ^ "\n" ^ compile_info expname
  in
    (print_endline infos; writel (expdir ^ "/stats") [infos])
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
   Export theorem data
   ------------------------------------------------------------------------ *)

(*
load "tttUnfold"; open tttUnfold aiLib;

val tactictoe_dir = HOLDIR ^ "/src/tactictoe";
val thmdata_dir = tactictoe_dir ^ "/thmdata";
val _ = clean_dir thmdata_dir;

aiLib.load_sigobj ();
fun ttt_ancestry thy =
  filter (fn x => not (mem x ["min","bool"])) (sort_thyl (ancestry thy))

fun ttt_record_thmdata () =
  let
    val thyl1 = ttt_ancestry (current_theory ())
    val ((),t) = add_time (app ttt_record_thy) thyl1
  in
    print_endline ("ttt_record time: " ^ rts_round 4 t)
  end;

tttSetup.record_flag := false;
tttSetup.record_savestate_flag := false;
tttSetup.export_thmdata_flag := true;
ttt_record_thmdata ();
*)


(* ------------------------------------------------------------------------
   Evaluation on one example
   ------------------------------------------------------------------------ *)

(*
load "tttEval"; open aiLib tttSetup tttEval;
val smlfun = "tttEval.ttt_eval";
val expname = "test14";
val savestatedir = tactictoe_dir ^ "/savestate";
val expdir = ttt_eval_dir ^ "/" ^ expname;
val outdir = expdir ^ "/out"
val valdir = expdir ^ "/val"
val argdir = expdir ^ "/arg"
val tnndir = expdir ^ "/tnn"
val pbdir = expdir ^ "/pb"
val _ = app mkDir_err
  [ttt_eval_dir, expdir, outdir, valdir, argdir, pbdir, tnndir];
val file = savestatedir ^ "/" ^ "relation_40";
tttSetup.ttt_search_time := 30.0;
tttSetup.ttt_metis_flag := true;
tttSetup.ttt_policy_coeff := 0.5;
hh_flag := false;
hh_ontop_flag := true;
hh_timeout := 10;
run_evalscript smlfun expdir (NONE,NONE,NONE) file;
*)


(* ------------------------------------------------------------------------
   Evaluation on a list of files
   ------------------------------------------------------------------------ *)

(*
load "tttEval"; open tttEval;

val smlfun = "tttEval.ttt_eval";
tttSetup.ttt_search_time := 30.0;
tacticToe.hh_use := false; tacticToe.hh_time := 5;
tttSetup.ttt_metis_flag := true;
tttSetup.ttt_policy_coeff := 0.5;
hh_flag := false; hh_timeout := 530;
hh_ontop_flag := true; tttSearch.snap_flag := true; tttSearch.snap_n := 100;

val savestatedir = tttSetup.tactictoe_dir ^ "/savestate";
val evaldir = tttSetup.tactictoe_dir ^ "/eval";
val filel = aiLib.readl (evaldir ^ "/hard_avail");
fun trim s = savestatedir ^ "/" ^
  String.substring (s,12,String.size s - 5 - 12);
val filel2 = map trim filel;

run_evalscript_filel smlfun "hard-seq" (true,20)
  (NONE,NONE,NONE) filel2;

*)

(*
load "aiLib"; open aiLib;
val sl = readl "time";
val sl1 = map (fn x => snd (split_string " " x)) sl;
val rl = map (valOf o Real.fromString) sl1;
val rl1 = dict_sort Real.compare rl;
fun rltograph n rl = case rl of
    [] => []
  | a :: m => (a - 0.0001, n) :: (a,n+1) :: rltograph (n+1) m

fun write_graph file (s1,s2) l =
  writel file ((s1 ^ " " ^ s2) :: map (fn (a,b) => rts a ^ " " ^ its b) l)
write_graph  (HOLDIR ^ "/src/tactictoe/eval/graph/hard-eprover-1_graph")
  ("time","proofs") (rltograph 0 rl1);
*)

(* ------------------------------------------------------------------------
   Reinforcement learning of the value of an intermediate goal.
   ------------------------------------------------------------------------ *)

fun rl_schedule nepoch =
   [
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 16, nepoch = nepoch},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 24, nepoch = nepoch},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 32, nepoch = nepoch},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 48, nepoch = nepoch},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 64, nepoch = nepoch}
   ];


fun tnnex_to_basicex ex =
  let fun f ex = case ex of
    [(t,[r])] => (t,r)
  | _ => raise ERR "not a basic example" ""
  in
    map f ex
  end

fun uniq_ex ex =
  let
    val ex1 = tnnex_to_basicex ex
    val _ = print_endline ("Examples: " ^ its (length ex1))
    val ex2 = dlist (dregroup Term.compare ex1)
    fun f (t,l) = if exists (fn x => x > 0.5) l then (t,1.0) else (t,0.0)
    val ex3 = map f ex2
    val _ = print_endline ("Unique: " ^ its (length ex3))
  in
    basicex_to_tnnex ex3
  end

fun train_fixed pct exl' =
  let
    val exl = uniq_ex exl'
    val (train,test) = part_pct pct (shuffle exl)
    fun operl_of_tnnex exl =
      List.concat (map operl_of_term (map fst (List.concat exl)))
    val operl = operl_of_tnnex exl
    val operset = mk_fast_set (cpl_compare Term.compare Int.compare) operl
    val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operset
    val randtnn = random_tnn operdiml
    val nepoch = 20
    val tnn = train_tnn (rl_schedule nepoch) randtnn (train,test)
    val accur = tnn_accuracy tnn train
  in
    print_endline ("tnn accuracy:" ^ rts accur);
    tnn
  end

fun collect_ex dir =
  let val filel = map (fn x => dir ^ "/" ^ x) (listDir dir) in
    List.concat (map read_tnnex filel)
  end

val ttt_eval_string = "tttEval.ttt_eval"

fun rlval_loop ncore expname thyl (gen,maxgen) =
  if gen > maxgen then () else
  let
    fun gendir x = ttt_eval_dir ^ "/" ^ expname ^ "-gen" ^ its x
    fun valdir x = gendir x ^ "/val"
    val dirl = List.tabulate (gen,valdir)
    val exl = List.concat (map collect_ex dirl)
    val tnnfile = gendir (gen - 1) ^ "/tnn/val"
    val hidfile = gendir (gen - 1) ^ "/train_log"
    val _ = erase_file hidfile
    val tnn = hide_in_file hidfile (train_fixed 1.0) exl
    val _ = write_tnn tnnfile tnn
  in
    print_endline ("Generation " ^ its gen);
    run_evalscript_thyl ttt_eval_string
      (expname ^ "-gen" ^ its gen) (true,ncore)
    (SOME tnnfile,NONE,NONE) thyl;
    rlval_loop ncore expname thyl (gen+1,maxgen)
  end

fun rlval ncore expname thyl maxgen =
  (
  print_endline ("Generation 0");
  run_evalscript_thyl ttt_eval_string (expname ^ "-gen0") (true,ncore)
    (NONE,NONE,NONE) thyl;
  rlval_loop ncore expname thyl (1,maxgen)
  )

(*
load "tttUnfold"; open tttUnfold;
(* aiLib.load_sigobj (); *)
tttSetup.record_flag := false;
tttSetup.record_savestate_flag := true;
ttt_record_savestate (); (* includes clean savestate *)
*)

(*
load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
(* smlOpen.buildheap_options := "--maxheap 4000"; *)
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val ncore = 30;
val _ = tttSearch.default_reward := 1.0;
val expname = "altreward3";
*)


(*
run_evalscript_thyl "tttEval.ttt_eval" expname (true,30)
  (NONE,NONE,NONE) thyl;

(* see Training test *)

run_evalscript_thyl "tttEval.ttt_eval" expname (true,30)
  (SOME (tnnfile expname),NONE,NONE) thyl;
*)

(*
rlval ncore expname thyl 1;
*)

(*
rlval_loop expname thyl (1,maxgen);
*)


(* ------------------------------------------------------------------------
   Training test
   ------------------------------------------------------------------------ *)

(*
open mlTreeNeuralNetwork aiLib;;

val expdir = tttSetup.ttt_eval_dir ^ "/" ^ expname;
fun tnnfile expname = tttSetup.ttt_eval_dir ^ "/" ^ expname ^ "/tnn/val";

val exl1 = collect_ex valdir;
val exl2 = uniq_ex exl1;
val oper_compare = (cpl_compare Term.compare Int.compare);
val operl = List.concat (map operl_of_term (map fst (List.concat exl2)));
val operset = mk_fast_set oper_compare operl;
val (train,test) = part_pct 0.9 (shuffle exl2);

fun train_fixed schedule =
  let
    val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operset
    val randtnn = random_tnn operdiml
    val tnn = train_tnn schedule randtnn (train,test)
  in
    tnn
  end;

val schedule =
    [{ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 16, nepoch = 20},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 24, nepoch = 20},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 32, nepoch = 20},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 48, nepoch = 20},
     {ncore = 4, verbose = true,
     learning_rate = 0.08, batch_size = 64, nepoch = 20}];
val tnn = train_fixed schedule;
tnn_accuracy tnn train;
tnn_accuracy tnn test;

val _ = write_tnn (tnnfile expname) tnn;
*)



end (* struct *)
