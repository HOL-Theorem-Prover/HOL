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
  nntm_of_sit: 'a psMCTS.sit -> term,
  mk_targetl: int -> 'a psMCTS.sit list 
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

fun bts b = if b then "true" else "false"

(* -------------------------------------------------------------------------
   Hard-coded parameters
   ------------------------------------------------------------------------- *)

val ngen_glob = ref 20
val ntarget_compete = ref 400
val ntarget_explore = ref 400

val exwindow_glob = ref 40000
val uniqex_flag = ref true
val dim_glob = ref 8
val batchsize_glob = ref 64
val nepoch_glob = ref 100
val lr_glob = ref 0.1
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
    val nn0   = "uniqex_flag: " ^ bts (!uniqex_flag)
    val nn1   = "example_window: " ^ its (!exwindow_glob)
    val nn2   = "nn dim: " ^ its (!dim_glob)
    val nn3   = "nn batchsize: " ^ its (!batchsize_glob)
    val nn4   = "nn epoch: " ^ its (!nepoch_glob)
    val nn6   = "nn lr: " ^ rts (!lr_glob)
    val nn5   = "nn ncore: " ^ its (!ncore_train_glob)
    val mcts2 = "mcts simulation: " ^ its (!nsim_glob)
    val mcts3 = "mcts decay: " ^ rts (!decay_glob)
    val mcts4 = "mcts ncore: " ^ its (!ncore_mcts_glob)
  in
    summary "Global parameters";
    summary (String.concatWith "\n  " 
     ([file] @ [gen1,gen2,gen3] @ [nn0,nn1,nn2,nn3,nn4,nn6,nn5] @ 
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
    (* if startb 
    then (1.0, filter_sit (map (fn x => (x,1.0)) movel))
    else *)
     (only_hd (infer_tnn etnn nntm),
      filter_sit (combine (movel, infer_tnn ptnn nntm)))
  end

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

val emptyallex = []

fun complete_pol movel mrl =
  let fun f move = assoc move mrl handle HOL_ERR _ => 0.0 in
    map f movel
  end

fun add_rootex gamespec tree allex =
  let  
    val root = dfind [0] tree
    val sit  = #sit root
    val nntm = (#nntm_of_sit gamespec) sit
    val movel = #movel gamespec
  in
    case evalpoli_example tree of
      NONE    => allex
    | SOME (e,p) => (nntm,[e],complete_pol movel p) :: allex
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)
val verbose_flag = ref false

fun n_bigsteps_loop (n,nmax) gamespec mctsparam (allex,allroot) tree =
  if n >= nmax then (allex,allroot) else
  let
    val nntm_of_sit = #nntm_of_sit gamespec
    val sit = #sit (dfind [0] tree)
    val newtree = mcts mctsparam tree
    val root = dfind [0] newtree
    val filter_sit = (#filter_sit gamespec) sit
    val _ = if !verbose_flag then print_endline (tts (nntm_of_sit sit)) else ()
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
          val newallex = add_rootex gamespec newtree allex
        in
          n_bigsteps_loop (n+1,nmax) gamespec mctsparam
          (newallex, root :: allroot) cuttree
        end
    end
  end

(*
val cost1 = rlGameArithGround.total_cost_target target
val cost2 = 2 * cost1 + 5
*)

fun n_bigsteps gamespec mctsparam target =
  let val tree = starttree_of mctsparam target in
    n_bigsteps_loop (0,64) gamespec mctsparam (emptyallex,[]) tree
  end

(* -------------------------------------------------------------------------
   Exploration functions
   ------------------------------------------------------------------------- *)

fun explore_test dhtnn target =
  let
    val (noise,bstart) = (false,false)
    val gamespec = rlAimModel.gamespec
    val status_of = #status_of gamespec
    val mctsparam =
      (!nsim_glob, !decay_glob, noise,
       #status_of gamespec, #apply_move gamespec, 
       mk_fep_dhtnn bstart gamespec dhtnn)
  in
    verbose_flag := true;
    ignore (n_bigsteps gamespec mctsparam target);
    verbose_flag := false 
  end

fun explore_extern (wid,job) flags dhtnn target =
  let
    val (noise,bstart) = flags
    val gamespec = rlAimModel.gamespec
    val status_of = #status_of gamespec
    val mctsparam =
      (!nsim_glob, !decay_glob, noise,
       #status_of gamespec, #apply_move gamespec, 
       mk_fep_dhtnn bstart gamespec dhtnn)
    val (exl,rootl) = n_bigsteps gamespec mctsparam target
    val endroot = hd rootl
    val bstatus = status_of (#sit endroot) = Win
  in
    write_dhex (widexl_file (wid,job)) exl;
    writel_atomic (widwin_file (wid,job)) [bstatus_to_string bstatus];
    writel_atomic (widout_file wid) ["done"] 
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun epex_stats epex =
  let  
    val d = count_dict (dempty Term.compare) (map #1 epex)
    val r = average_real (map (Real.fromInt o snd) (dlist d))
  in
    summary ("examples: " ^ its (length epex));
    summary ("average duplicates: " ^ rts r)
  end

fun random_dhtnn_gamespec gamespec =
  random_dhtnn (!dim_glob, length (#movel gamespec)) (#operl gamespec)

fun train_dhtnn gamespec epex =
  let
    val _ = epex_stats epex
    val schedule = [(!nepoch_glob, !lr_glob / Real.fromInt (!batchsize_glob))]
    val bsize = 
      if length epex < !batchsize_glob then 1 else !batchsize_glob
    val dhtnn = random_dhtnn_gamespec gamespec
  in
    train_dhtnn_schedule (!ncore_train_glob) dhtnn bsize epex schedule
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

(*
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
*)

(* -------------------------------------------------------------------------
   Additional communication files
   ------------------------------------------------------------------------- *)

fun dhtnn_file () = !parallel_dir ^ "/dhtnn"
fun targetl_file () = !parallel_dir ^ "/targetl"
fun widexl_file (wid,job) = wid_dir wid ^ "/exl" ^ its job
fun widwin_file (wid,job) = wid_dir wid ^ "/win" ^ its job

(* -------------------------------------------------------------------------
   External parallelization of competition/explorationn calls
   ------------------------------------------------------------------------- *)

fun bstatus_to_string b = if b then "win" else "lose"
fun string_to_bstatus s = assoc s [("win",true),("lose",false)]
  handle HOL_ERR _ => raise ERR "string_to_bstatus" ""
fun flags_to_string (b1,b2) = "(" ^ bts b1 ^ "," ^  bts b2 ^ ")"

fun codel_of flags wid = 
    [
     "open rlEnv;",
     "val _ = parallel_dir := " ^ quote (!parallel_dir) ^ ";",
     "val _ = nsim_glob := " ^ its (!nsim_glob) ^ ";",
     "val _ = decay_glob := " ^ rts (!decay_glob) ^ ";",
     "val _ = dim_glob := " ^ its (!dim_glob) ^ ";",
     "val _ = ntarget_explore := " ^ its (!ntarget_explore) ^ ";",    
     "val _ = ntarget_compete := " ^ its (!ntarget_compete) ^ ";",
     "val dhtnn = read_dhtnn (dhtnn_file ())",
     "val l = mk_targetl (Int.max (!ntarget_explore, !ntarget_compete));",
     "val flags = " ^ flags_to_string flags ^ ";",  
     "fun f (wid,job) target =",
     "  explore_extern (wid,job) flags dhtnn target" 

     "val l = "
     "val _ = worker_start " ^  ^ " " ^ its wid ^ ";"
    ]

fun read_result_extern (wid,job) =
  let 
    val win = string_to_bstatus (hd (readl (widwin_file (wid,job))))
    val dhex = read_dhex (widexl_file (wid,job))
  in
    app remove_file [widwin_file (wid,job),widexl_file (wid,job)];
    (win,dhex)
  end

fun init_extern () = write_dhtnn (dhtnn_file ()) dhtnn

val attrib = [Thread.InterruptState Thread.InterruptAsynch, Thread.EnableBroadcastInterrupt true]

parmap_queue_extern ncore codel_of (init,rr)

(*

load "smlParallel"; open aiLib smlParallel;

val gamespec = 5;
val dhtnn = random_dhtnn gamespec;




fun rr (wid,job) = string_to_int (hd (readl_rm (result_file (wid,job))));

fun codel_of wid = 
  [
   "open smlParallel;",
   "val dhtnn = read



   "fun g x = x + 1;",
   "fun f (wid,job) x =", 
   "  (writel_atomic (result_file (wid,job)) [aiLib.its (g x)];",
   "   writel_atomic (widout_file wid) [\"done\"]);",
   "val l = generate_targets ();",
   "worker_start " ^ (its wid) ^ " (f,l);"
  ]
;

val l = List.tabulate (100,I);

val ncore = 2;
val (l1,t) = add_time (parmap_queue_extern ncore codel_of (init,rr)) l;
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
    (* val levelup = int_div (Int.max (w_new,w_old)) (length selectl) > 0.75 *)
  in
    summary_compete (w_old,w_new);
    (* if levelup then incr level_glob else (); *)
    if w_new > w_old then dhtnn_new else dhtnn_old
  end

(* -------------------------------------------------------------------------
   Exploration.
   ------------------------------------------------------------------------- *)

val uniqex_flag = ref false

fun explore_f_aux startb gamespec allex dhtnn selectl =
  let
    val ((nwin,exll),t) = add_time
      (boss_start (!ncore_mcts_glob) (true,startb) dhtnn) selectl 
    val _ = summary ("Exploration time: " ^ rts t)
    val _ = summary ("Exploration wins: " ^ its nwin)
    fun cmp ((a,_,_),(b,_,_)) = Term.compare (a,b)
    val exl1 = List.concat exll @ allex
    val exl2 =  if !uniqex_flag then mk_sameorder_set cmp exl1 else exl1
  in
    first_n (!exwindow_glob) exl2
  end

fun explore_eval ncore dhtnn targetl =
  let val i = fst (boss_start ncore (false,false) dhtnn targetl) in
    Real.fromInt i / Real.fromInt (length targetl)
  end

fun explore_f startb gamespec allex dhtnn targetl =
  let val selectl = first_n (!ntarget_explore) (shuffle targetl) in
    explore_f_aux startb gamespec allex dhtnn selectl
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

(*
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
*)

fun rl_start gamespec =
  let
    val _ = remove_file (eval_dir ^ "/" ^ (!logfile_glob))
    val _ = summary_param ()
    val _ = summary "Generation 0"
    val dhtnn_random = random_dhtnn_gamespec gamespec
    val mk_targetl = #mk_targetl gamespec
    val targetl = mk_targetl (Int.max (!ntarget_explore, !ntarget_compete))
    val allex = explore_f true gamespec emptyallex dhtnn_random targetl
    val dhtnn = train_f gamespec allex
  in
    (allex , dhtnn, targetl)
  end

fun rl_one n gamespec (allex,dhtnn,targetl) =
  let
    val _ = summary ("\nGeneration " ^ its n)
    val dhtnn_new = train_f gamespec allex
    (* val dhtnn_best = compete dhtnn dhtnn_new gamespec targetl *)
    val mk_targetl = #mk_targetl gamespec
    val targetl_new = 
      mk_targetl (Int.max (!ntarget_explore, !ntarget_compete))
    val newallex = explore_f false gamespec allex dhtnn_new targetl_new
  in
    (newallex, dhtnn_new, targetl_new)
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

end (* struct *)

(*
load "rlEnv";
open rlEnv;

logfile_glob := "april16";
rl_gencode_dir := (!rl_gencode_dir) ^ (!logfile_glob);

ncore_mcts_glob := 2;
ncore_train_glob := 2;
ngen_glob := 100;
ntarget_compete := 100;
ntarget_explore := 100;
exwindow_glob := 40000;
uniqex_flag := false;
dim_glob := 8;
batchsize_glob := 2;
nepoch_glob := 100;
lr_glob := 0.1;
nsim_glob := 1600;
decay_glob := 1.0;

val (allex,dhtnn,targetl) = start_rl_loop rlAimModel.gamespec;

write_dhtnn "save" dhtnn;

(* todo: flags for nbig_steps and n_epoch *)
*)

(* parmap error = batch of 100 *)


