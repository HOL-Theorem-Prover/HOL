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
  tttSetup tttSearch tttRecord tacticToe tttToken tttTrain tttBigSteps

val ERR = mk_HOL_ERR "tttEval"
fun catch_err msg f x = 
  f x handle HOL_ERR {origin_structure,origin_function,message} => 
  (print_endline 
    (msg ^ ":" ^ origin_structure ^ ":" ^ origin_function ^ ":" ^ message);
  raise ERR "tttEval" "error caught (see log)")

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
val export_pb_flag = ref false

(* --------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------ *)

fun is_proof x = (case x of Proof _ => true | _ => false)

val keyl = ["nodes:","loops:",
  "search:","select:","exparg:","apply:","create:","backup:","recons:",
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
    create = parse_real "create:" (List.nth (l,6)),
    backup = parse_real "backup:" (List.nth (l,7)),
    recons = parse_real "recons:" (List.nth (l,8)),
    metis = parse_real "metis:" (List.nth (l,9)),
    other = parse_real "other:" (List.nth (l,10)),
    status = parse_status "tactictoe:" (List.nth (l,11))
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
    "create " ^ rts_round 6 (sum_real (map #create statsl) / totsearch),
    "backup " ^ rts_round 6 (sum_real (map #backup statsl) / totsearch),
    "recons_average " ^ rts_round 6 (sum_real (map #recons statsl) / 
       Real.fromInt (length provenl)),
    "metis " ^ rts_round 6 (sum_real (map #metis statsl) / totsearch),
    "other " ^ rts_round 6 (sum_real (map #other statsl) / totsearch)]
  end

(* load "tttEval"; open tttEval aiLib;
   print_endline (compile_info "210127-1"); *)

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
    val stim1 = valOf (List.find (String.isPrefix "search: ") sl)
    val stim2 = snd (split_string "search: " stim1)
    val t = valOf (Real.fromString stim2)
  in
    (snd (split_string "buildheap_" file), (status,t))
  end

fun write_graph file (s1,s2) l =
  writel file ((s1 ^ " " ^ s2) :: map (fn (a,b) => rts a ^ " " ^ its b) l)

fun stats_exp exp =
  let
    val dir = ttt_eval_dir ^ "/" ^ exp ^ "/out"
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

(* -------------------------------------------------------------------------
   TNN value examples
   ------------------------------------------------------------------------- *)

fun is_proved tree = #nstatus (dfind [] tree) = NodeProved

fun export_valex file tree =
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
   Argument policy examples
   ------------------------------------------------------------------------- *)

fun access_child argtree anl i = dfind (i :: anl) argtree

(*
fun export_argex file tree =
  if not (is_proved tree) then () else 
  let
    val nodel = map snd (dlist tree)
    fun f_arg g stac x = 
      if true (* #svis x > 1.5 orelse #sstatus x = StacProved *) 
      then SOME (nntm_of_statearg ((g,stac),#token x),
                 if #sstatus x = StacProved then [1.0] else [0.0])
      else NONE
    fun f_argtree g x = 
      if #sstatus (dfind [] x) <> StacProved then NONE else
      let 
        val stac = dest_stac (#token (dfind [] x))  
        val argl = map snd (before_stacfresh_all 
          (access_child x []))             
        val exo = 
          if length argl <= 1 then NONE else 
          let val ex = List.mapPartial (f_arg g stac) argl in
            if length ex <= 1 then NONE else SOME ex
          end
      in
        exo
      end
    fun f_goal x = List.concat (List.mapPartial
       (f_argtree (#goal x)) (vector_to_list (#stacv x)))
    fun f_node x = map f_goal (vector_to_list (#goalv x))
    val exl = List.concat (map f_node nodel)
  in
    write_tnnex file exl
  end
*)
(* -------------------------------------------------------------------------
   Exporting problems on intermediate goals
   ------------------------------------------------------------------------- *)

fun mk_info (id,gi,gstatus,gvis) =
  ["Path: " ^ (if null id then "top" else string_of_id id),
   "Goal: " ^ its gi,
   "Status: " ^ (if gstatus = GoalProved then "proven" else "unknown"),
   "Visits: " ^ rts gvis]

fun export_pb pbprefix pbn (g,(id,gi,gstatus,gvis)) =
  let 
    val pbfile = pbprefix ^ "-" ^ its pbn
    val premises = mlNearestNeighbor.thmknn_wdep 
      (!thmdata_glob) 128 (mlFeature.fea_of_goal true g) 
  in
    export_goal (pbfile ^ ".goal") g;
    writel (pbfile ^ ".premises") premises;
    writel (pbfile ^ ".info") (mk_info (id,gi,gstatus,gvis))
  end

fun export_pbl pbprefix tree =
  if not (can (smlExecute.tactic_of_sml 1.0) "metisTools.METIS_TAC []") 
  then () else
  let
    fun f id (gi,x) = (#goal x, (id, gi, #gstatus x, #gvis x))    
    fun g (id,x) = vector_to_list (Vector.mapi (f id) (#goalv x))
    val pbl = List.concat (map g (dlist tree))
    fun cmp (a,b) = Real.compare (#4 (snd b),#4 (snd a))
    val pbl_sorted = first_n 32 (dict_sort cmp pbl)
  in
    appi (export_pb pbprefix) pbl_sorted
  end

(* -------------------------------------------------------------------------
   Goal tree up to a maximum width + depth
   ------------------------------------------------------------------------- *)

datatype GoalDisj = GDisj of goal * GoalConj list
and GoalConj = GConj of GoalDisj list

fun children_of_argtree maxw tree id (gn,sn) argtree =
  let 
    val anll = dkeys argtree
    fun prefix anl = (gn,sn,anl) :: id
    fun test anl = dmem (prefix anl) tree
    val anll1 = filter test anll
    val anll2 = dict_sort (list_compare Int.compare) anll1
  in
    map prefix (first_n maxw anll2)
  end

fun children_of_stacv maxw tree id gn sn argtreel = 
   if maxw <= 0 then [] else
   case argtreel of
     [] => []
   | argtree :: m => 
     let val cidl = children_of_argtree maxw tree id (gn,sn) argtree in
       if null cidl 
       then children_of_stacv maxw tree id gn (sn+1) m
       else cidl :: children_of_stacv (maxw - 1) tree id gn (sn+1) m
     end

fun mk_goaltree maxw tree id =
  let
    val node = dfind id tree
    val goalv = number_snd 0 (vector_to_list (#goalv node))
    fun f (x,i) = if #gstatus x <> GoalProved then SOME (x,i) else NONE
    val goall = List.mapPartial f goalv
    fun g (grec,gn) = 
      let val cidl = List.concat 
        (children_of_stacv maxw tree id gn 0 (vector_to_list (#stacv grec)))
      in
        if maxw - 1 <= 0 
        then GDisj (#goal grec, [])
        else GDisj (#goal grec, map (mk_goaltree (maxw - 1) tree) cidl)
      end
  in
    GConj (map g goall)
  end

(* -------------------------------------------------------------------------
   Convert goal tree to a term
   ------------------------------------------------------------------------- *)

fun gen_term t = list_mk_forall (free_vars_lr t, t)
fun termify g = gen_term (list_mk_imp g)

fun termify_gconj gconj = case gconj of
  GConj gdisjl => 
    if null gdisjl then raise ERR "termify_goaltree" "unexpected" else 
    list_mk_conj (map termify_gdisj gdisjl)
and termify_gdisj gdisj = case gdisj of
  GDisj (goal,gconjl) => 
    list_mk_disj (termify goal :: map termify_gconj gconjl)

(* -------------------------------------------------------------------------
   Evaluation function
   ------------------------------------------------------------------------- *)

fun print_status r = case r of
   ProofSaturated => print_endline "tactictoe: saturated"
 | ProofTimeout   => print_endline "tactictoe: timeout"
 | Proof s        => print_endline ("tactictoe: proven\n  " ^ s)

val hh_flag = ref false
val hh_ontop_flag = ref false
val hh_ontop_wd = ref 1

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
    val _ = app mkDir_err [expdir ^ "/fof", fofdir]
    val mem = !hide_flag
    val _ = hide_flag := false
    val _ = print_endline ("ttt_eval: " ^ string_of_goal goal)
    val _ = print_endline ("ttt timeout: " ^ rts (!ttt_search_time))
  in
    if !hh_flag then hh_call fofdir thmdata goal else
    let val ((status,tree),t) = add_time
      (main_tactictoe (thmdata,tacdata) nnol) goal
      handle Interrupt => raise Interrupt
        | e => (print_endline "Error"; raise e)
    in
      print_status status;
      print_endline ("ttt_eval: " ^ rts_round 6 t);
      export_valex valfile tree;
      (* export_argex argfile tree; *)
      if !export_pb_flag then export_pbl pbprefix tree else ();
      (* call to holyhammer on partial proof tree *)
      if !hh_ontop_flag andalso not (is_proved tree) 
      then 
        let 
          fun build_term () =
            ([], termify_gconj (mk_goaltree (!hh_ontop_wd) tree []))
          val newgoal = catch_err "build_term" build_term ()
        in 
          catch_err "hh_call" (hh_call fofdir thmdata) newgoal 
        end
      else ()
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
     sreflect_real "tttSearch.ttt_vis_fail" ttt_vis_fail,
     sreflect_flag "tttSetup.ttt_metis_flag" ttt_metis_flag,
     sreflect_flag "tttSearch.ttt_spol_flag" ttt_spol_flag,
     sreflect_flag "aiLib.debug_flag" debug_flag,
     sreflect_flag "tttEval.export_pb_flag" export_pb_flag,
     sreflect_flag "tttEval.cheat_flag" cheat_flag,
     sreflect_flag "tttEval.hh_flag" hh_flag,
     sreflect_int "tttEval.hh_timeout" hh_timeout,
     sreflect_flag "tttEval.hh_ontop_flag" hh_ontop_flag,
     sreflect_int "tttEval.hh_ontop_wd" hh_ontop_wd,
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
    val _ = print_endline ("evaluation: " ^ its (length filel2) ^ " problems")
    val (_,t) = add_time
      (parapp_queue ncore (run_evalscript smlfun expdir nnol)) filel2
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
val expname = "test8";
val savestatedir = tactictoe_dir ^ "/savestate";
val expdir = ttt_eval_dir ^ "/" ^ expname;
val outdir = expdir ^ "/out"
val valdir = expdir ^ "/val"
val argdir = expdir ^ "/arg"
val tnndir = expdir ^ "/tnn"
val pbdir = expdir ^ "/pb"
val _ = app mkDir_err 
  [ttt_eval_dir, expdir, outdir, valdir, argdir, pbdir, tnndir];
val file = savestatedir ^ "/" ^ "relation_43";
tttSetup.ttt_search_time := 30.0;
tttSetup.ttt_metis_flag := true;
tttSetup.ttt_policy_coeff := 0.5;
tttSearch.ttt_vis_fail := 1.0;
cheat_flag := false;
hh_flag := false;
hh_ontop_flag := true;
hh_ontop_wd := 8;
hh_timeout := 30;
run_evalscript smlfun expname (NONE,NONE,NONE) file;
*)

(* ------------------------------------------------------------------------
   Evaluation on a list of theories
   ------------------------------------------------------------------------ *)

(*
load "tttUnfold"; open tttUnfold;
tttSetup.record_flag := false;
tttSetup.record_savestate_flag := true;
ttt_record_savestate (); (* also cleans the savestate directory *)

load "tttEval"; open tttEval;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val smlfun = "tttEval.ttt_eval";
tttSetup.ttt_search_time := 30.0;
tttSetup.ttt_metis_flag := true;
tttSetup.ttt_policy_coeff := 0.5;
tttSearch.ttt_vis_fail := 1.0;
cheat_flag := false;
hh_flag := false;
hh_ontop_flag := true;
hh_ontop_wd := 8;
hh_timeout := 30;
run_evalscript_thyl smlfun "210313-wd8-1" (true,20) 
  (NONE,NONE,NONE) thyl;
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

fun train_fixed pct exl =
  let
    val (train,test) = part_pct pct (shuffle exl)
    fun operl_of_tnnex exl =
      List.concat (map operl_of_term (map fst (List.concat exl)))
    val operl = operl_of_tnnex exl
    val operset = mk_fast_set (cpl_compare Term.compare Int.compare) operl
    val operdiml = map (fn x => (fst x, dim_std_arity (1,16) x)) operset
    val randtnn = random_tnn operdiml
    val nepoch = (20 * 100 * 1000) div (length exl) 
    val nepoch' = if nepoch >= 1 then nepoch else 1
    val tnn = train_tnn (rl_schedule nepoch') randtnn (train,test)
  in
    tnn
  end

fun collect_ex dir = 
  let val filel = map (fn x => dir ^ "/" ^ x) (listDir dir) in
    List.concat (map read_tnnex filel)
  end

val ttt_eval_string = "tttEval.ttt_eval"

fun rlval_loop expname thyl (gen,maxgen) =
  if gen > maxgen then () else
  let 
    fun gendir x = ttt_eval_dir ^ "/" ^ expname ^ "-gen" ^ its x
    fun valdir x = gendir x ^ "/val"    
    val dirl = List.tabulate (gen,valdir)
    val exl = List.concat (map collect_ex dirl)
    val tnnfile = gendir (gen - 1) ^ "/tnn/val"
    val _ = if exists_file tnnfile then () (* for restarts *) else 
      write_tnn tnnfile (train_fixed 1.0 exl)
  in
    print_endline ("Generation " ^ its gen);
    run_evalscript_thyl ttt_eval_string (expname ^ "-gen" ^ its gen) (true,30) 
    (SOME tnnfile,NONE,NONE) thyl;
    rlval_loop expname thyl (gen+1,maxgen)
  end

fun rlval expname thyl maxgen =
  (
  print_endline ("Generation 0"); 
  tttSearch.ttt_vis_fail := 1.0;
  run_evalscript_thyl ttt_eval_string (expname ^ "-gen0") (true,30) 
    (NONE,NONE,NONE) thyl;
  tttSearch.ttt_vis_fail := 0.1;
  rlval_loop expname thyl (1,maxgen)
  )

(*
load "tttUnfold"; open tttUnfold;
tttSetup.record_flag := false;
tttSetup.record_savestate_flag := true;
ttt_record_savestate (); (* includes clean savestate *)

load "tttEval"; open tttEval;
tttSetup.ttt_search_time := 30.0;
val expname = "210124-1";
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val maxgen = 10;
rlval expname thyl maxgen;


(* rlval_loop expname thyl (1,maxgen); *)
*)

(* ------------------------------------------------------------------------
   Training test
   ------------------------------------------------------------------------ *)

(*
load "tttEval"; open tttEval; 
val ttt_eval_dir = HOLDIR ^ "/src/tactictoe/eval";
val expname = "210121-2"
val expdir = ttt_eval_dir ^ "/" ^ expname;
val valdir = expdir ^ "/val";
val tnnfile = expdir ^ "/tnn/val";

open mlTreeNeuralNetwork aiLib;
fun collect_ex dir = 
  let val filel = map (fn x => dir ^ "/" ^ x) (listDir dir) in
    List.concat (map read_tnnex filel)
  end;

val exl = collect_ex valdir;
val exl = filter (not o null) (collect_ex valdir); length exl;

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
val tnn = train_fixed schedule exl;
val _ = write_tnn tnnfile tnn;

load "tttEval"; open tttEval;
val ttt_eval_dir = HOLDIR ^ "/src/tactictoe/eval";
val expname = "210121-2"
val expdir = ttt_eval_dir ^ "/" ^ expname;
val valdir = expdir ^ "/val";
val tnnfile = expdir ^ "/tnn/val";
tttSetup.ttt_search_time := 30.0;
val thyl = aiLib.sort_thyl (ancestry (current_theory ()));
val smlfun = "tttEval.ttt_eval";
tttSetup.ttt_metis_flag := true;
tttSetup.ttt_policy_coeff := 0.5;
tttSearch.ttt_vis_fail := 0.1;
tttSearch.ttt_spol_flag := false;
run_evalscript_thyl smlfun "210121-2-13" (true,30) 
  (SOME tnnfile,NONE,NONE) thyl;

*)





end (* struct *)
