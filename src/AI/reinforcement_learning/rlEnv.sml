(* ========================================================================= *)
(* FILE          : rlEnv.sml                                                 *)
(* DESCRIPTION   : Environnement for reinforcement learning                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlEnv :> rlEnv =
struct

open HolKernel Abbrev boolLib aiLib rlLib psMCTS mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlEnv"

type ('a,''b,'c) gamespec =
  {
  movel : ''b list,
  string_of_move : ''b -> string,
  filter_sit : 'a psMCTS.sit -> ((''b * real) list -> (''b * real) list),
  status_of : ('a psMCTS.sit -> psMCTS.status),
  apply_move : (''b -> 'a psMCTS.sit -> 'a psMCTS.sit),
  operl : (term * int) list,
  nntm_of_sit: 'a psMCTS.sit -> term
  }

(* -------------------------------------------------------------------------
   Log
   ------------------------------------------------------------------------- *)

val logfile_glob = ref "rlEnv"
val eval_dir = HOLDIR ^ "/src/AI/reinforcement_learning/eval"
fun log_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end
fun summary s = (log_eval (!logfile_glob) s; print_endline s)

(* -------------------------------------------------------------------------
   Hard-coded parameters
   ------------------------------------------------------------------------- *)

val ngen_glob = ref 20
val ntarget_compete = ref 400
val ntarget_explore = ref 400

val exwindow_glob = ref 40000
val dim_glob = ref 8
val batchsize_glob = ref 64
val nepoch_glob = ref 100
val ncore_train_glob = ref 4

val nsim_glob = ref 1600
val decay_glob = ref 0.99
val ncore_mcts_glob = ref 8

fun summary_param () =
  let
    val file  = "  file: " ^ (!logfile_glob)
    val gen1  = "gen max: " ^ its (!ngen_glob)
    val gen2  = "target_compete: " ^ its (!ntarget_compete)
    val gen3  = "target_explore: " ^ its (!ntarget_explore)
    val nn1   = "example_window: " ^ its (!exwindow_glob)
    val nn2   = "nn dim: " ^ its (!dim_glob)
    val nn3   = "nn batchsize: " ^ its (!batchsize_glob)
    val nn4   = "nn epoch: " ^ its (!nepoch_glob)
    val nn5   = "nn ncore: " ^ its (!ncore_train_glob)
    val mcts2 = "mcts simulation: " ^ its (!nsim_glob)
    val mcts3 = "mcts decay: " ^ rts (!decay_glob)
    val mcts4 = "mcts ncore: " ^ its (!ncore_mcts_glob)
  in
    summary "Global parameters";
    summary (String.concatWith "\n  " 
     ([file] @ [gen1,gen2,gen3] @ [nn1,nn2,nn3,nn4] @ 
      [mcts2,mcts3,mcts4])
     ^ "\n")
  end

(* -------------------------------------------------------------------------
   Evaluation and policy
   ------------------------------------------------------------------------- *)

fun mk_fep_dhtnn startb gamespec dhtnn sit =
  let
    val movel = #movel gamespec
    val filter_sit = (#filter_sit gamespec) sit
    val {opdict,headeval,headpoli,dimin,dimout} = dhtnn
    val etnn = {opdict=opdict,headnn=headeval,dimin=dimin,dimout=1}
    val ptnn = {opdict=opdict,headnn=headpoli,dimin=dimin,dimout=dimout}
    val nntm = (#nntm_of_sit gamespec) sit
  in
    if startb 
    then (0.05, filter_sit (map (fn x => (x,1.0)) movel))
    else (only_hd (infer_tnn etnn nntm),
      filter_sit (combine (movel, infer_tnn ptnn nntm)))
  end

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

val emptyallex = ([],[])

fun complete_pol movel mrl =
  let fun f move = assoc move mrl handle HOL_ERR _ => 0.0 in
    map f movel
  end

fun update_allex movel (nntm,(e,p)) (eex,pex) =
  ((nntm,[e]) :: eex, (nntm, complete_pol movel p) :: pex)

fun update_allex_from_tree gamespec tree allex =
  let
    val root = dfind [0] tree
    val sit  = #sit root
    val nntm = (#nntm_of_sit gamespec) sit
    val movel = #movel gamespec
  in
    case evalpoli_example tree of
      NONE    => allex
    | SOME ep => update_allex movel (nntm,ep) allex
  end

fun discard_oldex (a,b) n = (first_n n a, first_n n b)

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

fun n_bigsteps_loop (n,nmax) gamespec mctsparam (allex,allroot) tree =
  if n >= nmax then (allex,allroot) else
  let
    val nntm_of_sit = #nntm_of_sit gamespec
    val sit = #sit (dfind [0] tree)
    val newtree = mcts mctsparam tree
    val root = dfind [0] newtree
    val filter_sit = (#filter_sit gamespec) sit
    val movel = #movel gamespec
  in
   if null (filter_sit (map_assoc (fn x => 0.0) movel))
   then (allex, root :: allroot)
   else
     let val (dis,cido) = select_bigstep newtree [0] in
     case cido of
       NONE => (allex, root :: allroot)
     | SOME cid =>
        let
          val cuttree = cut_tree newtree cid
          val newallex = update_allex_from_tree gamespec newtree allex
        in
          n_bigsteps_loop (n+1,nmax) gamespec mctsparam
          (newallex, root :: allroot) cuttree
        end
    end
  end

fun n_bigsteps gamespec mctsparam target =
  let 
    val tree = starttree_of mctsparam target 
    val cost1 = rlGameArithGround.total_cost_target target
    val cost2 = 2 * cost1 + 5
  in
    n_bigsteps_loop (0,cost2) gamespec mctsparam (emptyallex,[]) tree
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun exl_stat (evalex,poliex) =
  let  
    val l1 = (dlist (dregroup Term.compare evalex))
    val r1 = average_real (map (Real.fromInt o length o snd) l1)
  in
    summary ("Average duplicates: " ^ rts r1);
    summary ("Eval examples: " ^ trainset_info evalex);
    summary ("Poli examples: " ^ trainset_info poliex)
  end

fun random_dhtnn_gamespec gamespec =
  random_dhtnn (!dim_glob, length (#movel gamespec)) (#operl gamespec)

fun train_dhtnn gamespec (evalex,poliex) =
  let
    val _ = exl_stat (evalex,poliex)
    val schedule = [(!nepoch_glob,0.1 / Real.fromInt (!batchsize_glob))]
    val bsize = if length evalex < (!batchsize_glob) then 1 
                else !batchsize_glob
    val dhtnn = random_dhtnn_gamespec gamespec
    val (etrain,ptrain) = (prepare_trainset evalex, prepare_trainset poliex)
  in
    train_dhtnn_schedule (!ncore_train_glob) 
      dhtnn bsize (etrain,ptrain) schedule
  end

fun train_f gamespec allex =
  let val (dhtnn,t) = add_time (train_dhtnn gamespec) allex in
    summary ("Training time : " ^ rts t); dhtnn
  end

(* -------------------------------------------------------------------------
   Results
   ------------------------------------------------------------------------- *)

(* todo: should return stats and examples in file out 
fun summary_wins gamespec allrootl =
  let
    val r0 = Real.fromInt (length allrootl)
    val endrootl = map hd allrootl
    val startrootl = map last allrootl
    fun value x = #sum x / #vis x
    val w5 = average_real (map value startrootl)
    val status_of = #status_of gamespec
    val w1 = length (filter (fn x => status_of (#sit x) = Win) endrootl)
    val w2 = length (filter (fn x => #status x = Win) endrootl)
    val w3 = length (filter (fn x => #status x = Win) (List.concat allrootl))
    val w4 = length (filter (fn x => #status x = Win) startrootl)
    val r1 = Real.fromInt (length (List.concat allrootl)) / r0
    val r2 = Real.fromInt w3 / r0
  in
    summary ("  Win start: " ^ its w4);
    summary ("  Value start (average): " ^ rts w5);
    summary ("  Win end: " ^ String.concatWith " " (map its [w1,w2]));
    summary ("  Big steps (average): " ^ rts r1);
    summary ("  Win nodes (average): " ^ rts r2)
  end
*)

(* -------------------------------------------------------------------------
   Adaptive difficulty
   ------------------------------------------------------------------------- *)

val level_glob = ref 1

fun eval_targetl gamespec dhtnn targetl =
  let
    val {opdict,headeval,headpoli,dimin,dimout} = dhtnn
    val etnn = {opdict=opdict,headnn=headeval,dimin=dimin,dimout=1}
    fun f sit = only_hd (infer_tnn etnn ((#nntm_of_sit gamespec) sit))
    val l = map_assoc f targetl    
    val r = rts (average_real (map snd l))
    val l2 = map (rlGameArithGround.total_cost_target) targetl
    val r2 = rts (average_real (map Real.fromInt l2))
  in
    summary ("  Average value (full dataset): " ^ r);
    summary ("  Average expected proof length (full dataset): " ^ r2);
    l
  end

fun interval (step:real) (a,b) =
  if a + (step / 2.0) > b then [b] else a :: interval step (a + step,b)

fun choose_uniform gamespec dhtnn (targetl,ntarget) =
  let
    val l = eval_targetl gamespec dhtnn targetl
    fun f r = map fst (filter (fn (_,x) => x >= r andalso x < r + 0.1) l)
    val ll0 = map f (interval 0.1 (0.0,0.9))
    val _ =
      summary ("  Repartition (self-assessed): " ^ String.concatWith " "
               (map (its o length) ll0))
    fun g x = part_n (ntarget div 10) (shuffle x)
    val ll1 = map g ll0
    val chosenl = List.concat (map fst ll1)
    val otherl = List.concat (map snd ll1)
  in
    chosenl @ first_n (ntarget - (length chosenl)) (shuffle otherl)
  end

(* -------------------------------------------------------------------------
   External parallelization of competition/explorationn calls
   ------------------------------------------------------------------------- *)

fun bstatus_to_string b = if b then "win" else "lose"
fun string_to_bstatus s = 
  assoc s [("win",true),("lose",false)]
  handle HOL_ERR _ => raise ERR "string_to_status" ""

fun writel_atomic file sl =
  (writel (file ^ "_temp") sl; 
   OS.FileSys.rename {old = file ^ "_temp", new=file})
fun readl_rm file =
  let val sl = readl file in OS.FileSys.remove file; sl end

val gencode_dir = HOLDIR ^ "/src/AI/reinforcement_learning/gencode"
val dhtnn_file = gencode_dir ^ "/dhtnn"
val targetl_file = gencode_dir ^ "/targetl"
fun widin_file wid = gencode_dir ^ "/" ^ its wid ^ "/in"
fun widout_file wid = gencode_dir ^ "/" ^ its wid ^ "/out"
fun widscript_file wid = 
  gencode_dir ^ "/" ^ its wid ^ "/script" ^ its wid ^ ".sml"
fun widexl_file wid = gencode_dir ^ "/" ^ its wid ^ "/exl"

(* Workers *)
fun explore_standalone flags wid dhtnn target =
  let
    val (noise,bstart) = flags
    val gamespec = rlGameArithGround.gamespec
    val status_of = #status_of gamespec
    val mctsparam =
      (!nsim_glob, !decay_glob, noise,
       #status_of gamespec, #apply_move gamespec, 
       mk_fep_dhtnn bstart gamespec dhtnn)
    val (exl,rootl) = n_bigsteps gamespec mctsparam target
    val endroot = hd rootl
    val bstatus = status_of (#sit endroot) = Win
  in
    write_dhtrainset (widexl_file wid) exl;
    writel_atomic (widout_file wid) [bstatus_to_string bstatus]     
  end

fun worker_process flags wid (dhtnn,targetl) i =
  (
  explore_standalone flags wid dhtnn (List.nth (targetl,i));
  worker_listen flags wid (dhtnn,targetl)
  )

and worker_listen flags wid (dhtnn,targetl) = 
  if exists_file (widin_file wid) 
  then 
    let val s = hd (readl_rm (widin_file wid)) in
      if s = "stop" then () else 
      worker_process flags wid (dhtnn,targetl) (string_to_int s)
    end 
  else (OS.Process.sleep (Time.fromReal 0.001); 
        worker_listen flags wid (dhtnn,targetl))

fun worker_start flags wid =
  let 
    val targetl = map rlGameArithGround.mk_startsit 
      (mlTacticData.import_terml targetl_file)
    val dhtnn = read_dhtnn dhtnn_file
    val _ = writel_atomic (widout_file wid) ["up"] 
  in
    worker_listen flags wid (dhtnn,targetl)
  end

(* Boss *)
fun boss_stop_workers threadl =
  let 
    val ncore = length threadl 
    fun send_stop wid = writel_atomic (widin_file wid) ["stop"] 
    fun loop threadl =
      (
      OS.Process.sleep (Time.fromReal (0.001));
      if exists Thread.isActive threadl then loop threadl else ()
      )
  in
    app send_stop (List.tabulate (ncore,I));
    loop threadl
  end

fun boss_end threadl completedl = 
  let 
    val ncore = length threadl
    val _ = print_endline ("stop " ^ its ncore ^ " workers")
    val _ = boss_stop_workers threadl
    val _ = print_endline ("  " ^ its ncore ^ " workers stopped")
    val l0 = dict_sort Int.compare (map fst completedl)
    val _ = print_endline 
      ("  completed jobs: " ^ String.concatWith " " (map its l0))
    val l1 = map snd completedl
    val nwin = length (filter (I o fst) l1)
    val exll = map snd l1
  in
    (nwin,exll)
  end

fun boss_readresult ((wid,job),x) =
  let val exl = read_dhtrainset (widexl_file wid) in
    (job, (string_to_bstatus (valOf x), exl))
  end

fun stat_jobs (remainingl,freewidl,runningl,completedl) = 
  print_endline
    ("target: " ^ its (length remainingl) ^ " "  ^ 
       its (length runningl) ^ " " ^ its (length completedl) ^ 
     " free core: " ^ String.concatWith " " (map its freewidl))

fun send_job (wid,job) = 
  if exists_file (widin_file wid) 
  then raise ERR "send_job" ""
  else 
    (
    print_endline ("  send job " ^ its job ^ " to worker " ^ its wid); 
    writel_atomic (widin_file wid) [its job]
    )

fun boss_send threadl (remainingl,runningl,completedl) =
  let
    fun is_running x = mem x (map fst runningl)
    val ncore = length threadl
    val freewidl = filter (not o is_running) (List.tabulate (ncore,I))
    val _ = stat_jobs (remainingl,freewidl,runningl,completedl)
    val njob = Int.min (length freewidl, length remainingl)
    val (jobl,remainingl_new) = part_n njob remainingl
    val runningl_new = combine (first_n njob freewidl, jobl)    
  in
    app send_job runningl_new;
    boss_collect threadl
      (remainingl_new, runningl_new @ runningl, completedl)
  end

and boss_collect threadl (remainingl,runningl,completedl) =
  if null remainingl andalso null runningl 
    then boss_end threadl completedl
  else
  let
    val _ = OS.Process.sleep (Time.fromReal 0.001)
    fun f (wid,job) =
      let val file = widout_file wid in
        if exists_file file 
        then 
          (print_endline 
           ("  completed job " ^ its job ^ " by worker " ^ its wid);  
           SOME (hd (readl_rm file))) 
        else NONE
      end
    val (al,bl) = partition (isSome o snd) (map_assoc f runningl)
  in
    if null al 
    then boss_collect threadl (remainingl,runningl,completedl)
    else 
      let
        val runningl_new = map fst bl
        val completedl_new = map boss_readresult al
      in
        if null remainingl 
        then boss_collect threadl
          (remainingl,runningl_new,completedl_new @ completedl)
        else boss_send threadl
          (remainingl,runningl_new,completedl_new @ completedl)
      end
  end

fun bts b = if b then "true" else "false"
fun flags_to_string (b1,b2) = "(" ^ bts b1 ^ "," ^  bts b2 ^ ")"

fun boss_start_worker flags wid =
  let
    val codel =
    [
     "open rlEnv;",
     "val _ = nsim_glob := " ^ its (!nsim_glob) ^ ";",
     "val _ = decay_glob := " ^ rts (!decay_glob) ^ ";",
     "val _ = dim_glob := " ^ its (!dim_glob) ^ ";",
     "val _ = worker_start " ^ flags_to_string flags ^ " " ^ its wid ^ ";"
    ]  
  in
    writel (widscript_file wid) codel;
    smlOpen.run_buildheap false (widscript_file wid);
    remove_file (widscript_file wid)
  end

val attrib = [Thread.InterruptState Thread.InterruptAsynch, Thread.EnableBroadcastInterrupt true]

fun rm_out wid = remove_file (widout_file wid) 

fun boss_wait_upl widl =
  let 
    fun is_up wid = hd (readl (widout_file wid)) = "up" handle Io _ => false 
  in
    if all is_up widl then app rm_out widl else boss_wait_upl widl
  end

fun boss_start ncore flags dhtnn targetl =
  let
    val remainingl = List.tabulate (length targetl,I)
    val _ = mkDir_err gencode_dir
    fun mk_local_dir wid = mkDir_err (gencode_dir ^ "/" ^ its wid) 
    val _ = app mk_local_dir (List.tabulate (ncore,I))
    fun rm wid = 
      (remove_file (widin_file wid); remove_file (widout_file wid))
    val _ = app rm (List.tabulate (ncore,I))
    val _ = write_dhtnn dhtnn_file dhtnn
    val _ = mlTacticData.export_terml targetl_file 
      (map rlGameArithGround.dest_startsit targetl)
    val _ = print_endline ("start " ^ its ncore ^ " workers")
    val widl = List.tabulate (ncore,I)
    fun fork wid = Thread.fork (fn () => boss_start_worker flags wid, attrib)
    val threadl = map fork widl
  in
    boss_wait_upl widl;
    print_endline ("  " ^ its ncore ^ " workers started");
    boss_send threadl (remainingl,[],[])
  end





(* todo: 
   wait for all the worker to be up. 
*)

(*
load "rlEnv"; open aiLib rlEnv;
val ncore = 2;
val targetl1 = rlGameArithGround.mk_targetl 1;
val targetl2 = first_n 100 (shuffle targetl1);
val dhtnn = random_dhtnn_gamespec rlGameArithGround.gamespec;
val (nwin,exll) = boss_start ncore (true,false) dhtnn targetl2;
val ntot = length completedl;
val nwin = length (filter I (map snd completedl));

*)

(* -------------------------------------------------------------------------
   Competition: comparing n dhtnn
   ------------------------------------------------------------------------- *)

fun compete_one dhtnn targetl =
  let val ((nwin,_),t) = add_time 
    (boss_start (!ncore_mcts_glob) (false,false) dhtnn) targetl 
  in
    summary ("Competition time : " ^ rts t); nwin
  end

fun summary_compete (w_old,w_new) =
  let val s = if w_new > w_old then "Passed" else "Failed" in
    summary (s ^ ": " ^ its w_old ^ " " ^ its w_new)
  end

fun compete dhtnn_old dhtnn_new gamespec targetl =
  let
    val selectl = first_n (!ntarget_compete) (shuffle targetl)
    val w_old = compete_one dhtnn_old selectl
    val w_new = compete_one dhtnn_new selectl
    val levelup = int_div (Int.max (w_new,w_old)) (length selectl) > 0.75
  in
    summary_compete (w_old,w_new);
    if levelup then incr level_glob else ();
    if w_new > w_old then dhtnn_new else dhtnn_old
  end

(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

fun update_allex exll allex =
  let
    fun concat_ex ((exE,exP),(allexE,allexP)) = (exE @ allexE, exP @ allexP)
    val exl1 = foldl concat_ex allex exll
    fun cmp (a,b) = Term.compare (fst a,fst b)
    val exl2 = (mk_sameorder_set cmp (fst exl1), 
                mk_sameorder_set cmp (snd exl1))
  in
    discard_oldex exl2 (!exwindow_glob)
  end

(* todo: change allex and split it when making batches *)
fun explore_f_aux startb gamespec allex dhtnn selectl =
  let
    val ((nwin,exll),t) = add_time
      (boss_start (!ncore_mcts_glob) (true,startb) dhtnn) selectl 
    val _ = summary ("Exploration time: " ^ rts t)
    val _ = summary ("Exploration wins: " ^ its nwin)
  in
    update_allex exll allex
  end

fun explore_f startb gamespec allex dhtnn targetl =
  let val selectl = choose_uniform gamespec dhtnn (targetl,!ntarget_explore) in
    explore_f_aux startb gamespec allex dhtnn selectl
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun update_targetl () =  
  let
    val _ = summary ("Level: " ^ its (!level_glob))
    val (targetl,t) = 
      add_time rlGameArithGround.mk_targetl (!level_glob);
    val _ = summary ("Creating " ^ its (length targetl) ^ " new targets" ^ 
            " in " ^ rts t ^ " seconds")
  in
    shuffle targetl
  end

fun rl_start gamespec =
  let
    val _ = remove_file (eval_dir ^ "/" ^ (!logfile_glob))
    val _ = summary_param ()
    val _ = summary "Generation 0"
    val dhtnn_random = random_dhtnn_gamespec gamespec
    val targetl = update_targetl ()
    val allex = explore_f true gamespec emptyallex dhtnn_random targetl
    val dhtnn = train_f gamespec allex
  in
    (allex , dhtnn, targetl)
  end

fun rl_one n gamespec (allex,dhtnn,targetl) =
  let
    val _ = summary ("\nGeneration " ^ its n)
    val dhtnn_new = train_f gamespec allex
    val dhtnn_best = compete dhtnn dhtnn_new gamespec targetl
    val targetl_new = update_targetl ()
    val newallex = explore_f false gamespec allex dhtnn_best targetl_new
  in
    (newallex, dhtnn_best, targetl_new)
  end

fun rl_loop (n,nmax) gamespec rldata =
  if n >= nmax then rldata else
    let val rldata_new = rl_one n gamespec rldata in
      rl_loop (n+1, nmax) gamespec rldata_new
    end

fun start_rl_loop gamespec =
  let val (allex,dhtnn,targetl) = rl_start gamespec in
    rl_loop (1,!ngen_glob) gamespec (allex,dhtnn,targetl)
  end

(* -------------------------------------------------------------------------
   Training speed test
   ------------------------------------------------------------------------- *)

fun random_example operl size =
  let 
    val polin = length (#movel rlGameArithGround.gamespec) 
    val tm = psTermGen.random_term operl (size,bool)
  in
    ((tm, [random_real ()]), 
     (tm, List.tabulate (polin,fn _ => random_real ())))
  end

(*
load "rlEnv";
load "Profile"; open aiLib Profile rlEnv;
dim_glob := 8;
val dhtnn = random_dhtnn_gamespec rlGameArithGround.gamespec;
val operl = map fst (dkeys (#opdict dhtnn));

val size = 15;
val nex = 12800;
val trainex = 
  split (List.tabulate (nex, fn _ => random_example operl size));
batchsize_glob := 128;
nepoch_glob := 1;

fun test_ncore n =
  (
  reset_all ();
  PolyML.fullGC ();
  ncore_train_glob := n;
  ignore (profile (its n) (train_dhtnn rlGameArithGround.gamespec) trainex);
  results ()
  );

val result1l = map test_ncore [32];

mlTreeNeuralNetwork.pmt_flag := true;
val result2l = map test_ncore [32];
mlTreeNeuralNetwork.pmt_flag := false;

mlTreeNeuralNetwork.pmb_flag := true;
val result3l = map test_ncore [32];
mlTreeNeuralNetwork.pmb_flag := false;

result1l;
result2l;
result3l;


*)

end (* struct *)

(*
load "rlEnv";
open rlEnv;

logfile_glob := "march16-run2";
ncore_mcts_glob := 16;
ncore_train_glob := 8;
ngen_glob := 50;
ntarget_compete := 100;
ntarget_explore := 100;
exwindow_glob := 40000;
dim_glob := 8;
batchsize_glob := 64;
nepoch_glob := 100;
nsim_glob := 1600;
decay_glob := 0.99;
level_glob := 1;

val allex = start_rl_loop rlGameArithGround.gamespec;

(* todo: flags for nbig_steps and n_epoch *)
*)


