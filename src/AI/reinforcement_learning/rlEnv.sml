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
  dim : int,
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

fun summary s = log_eval (!logfile_glob) s

(* -------------------------------------------------------------------------
   Hard-coded parameters
   ------------------------------------------------------------------------- *)

val ngen_glob = ref 20
val ntarget_glob = ref 400
val exwindow_glob = ref 20000
val bigsteps_glob = ref 50
val nsim_glob = ref 1600
val decay_glob = ref 0.99
val noise_flag = ref true
val tmsize_flag = ref false

fun bool_to_string b = if b then "true" else "false"

fun summary_param targetl =
  let 
    val file = "File: " ^ (!logfile_glob) 
    val s0 = "number_of_targets: " ^ (its (length targetl))
    val s1 = "example_window: " ^ its (!exwindow_glob)
    val s2 = "big_steps: " ^ its (!bigsteps_glob)
    val s3 = "simulation: " ^ its (!nsim_glob)
    val s4 = "decay: " ^ rts (!decay_glob)
    val s5 = "noise: " ^ bool_to_string (!noise_flag)
    val s5' = "term_size: " ^ bool_to_string (!tmsize_flag)
    val s6 = "max_generation: " ^ its (!ngen_glob)
    val s7 = "target_per_generation: " ^ its (!ntarget_glob)
  in
    summary "Global parameters";
    summary (String.concatWith "\n  " [file,s0,s6,s7,s1,s2,s3,s4,s5,s5'] ^
    "\n")
  end

(* -------------------------------------------------------------------------
   Evaluation and policy
   ------------------------------------------------------------------------- *)

fun mk_fep_dhtnn bstart gamespec dhtnn sit =
  let
    val movel = #movel gamespec
    val filter_sit = (#filter_sit gamespec) sit
    val {opdict,headeval,headpoli,dimin,dimout} = dhtnn
    val etnn = {opdict=opdict,headnn=headeval,dimin=dimin,dimout=1}
    val ptnn = {opdict=opdict,headnn=headpoli,dimin=dimin,dimout=dimout}
    val nntm = (#nntm_of_sit gamespec) sit
    fun f x = x / (1.0 + (Real.fromInt (term_size nntm) / 100.0))
  in
    if bstart then 
      ((if !tmsize_flag then f else I) 0.05, 
      filter_sit (map_assoc (fn x => 1.0) movel)) 
    else
    (
    (if !tmsize_flag then f else I) (only_hd (infer_tnn etnn nntm)), 
    filter_sit (combine (movel, infer_tnn ptnn nntm))
    )
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

fun n_bigsteps_loop (n,nmax) gamespec pbspec (allex,allroot) tree =
  if n >= nmax then (print_endline "Max depth\n"; (allex,allroot)) else
  let
    val nntm_of_sit = #nntm_of_sit gamespec
    val sit = #sit (dfind [0] tree)
    val _ = print_endline (its n ^ ": " ^ tts (nntm_of_sit sit))
    val newtree = mcts (!nsim_glob, !decay_glob, !noise_flag) pbspec tree
    val root = dfind [0] newtree
    val filter_sit = (#filter_sit gamespec) sit
    val movel = #movel gamespec
  in
   if null (filter_sit (map_assoc (fn x => 0.0) movel))
   then (print_endline "No move available\n"; (allex, root :: allroot))
   else
     let val (dis,cido) = select_bigstep newtree [0] in
     case cido of
       NONE => (allex, root :: allroot)
     | SOME cid =>
        let
          val _ = print_distrib (#string_of_move gamespec) dis
          val cuttree = cut_tree newtree cid
          val newallex = update_allex_from_tree gamespec newtree allex
        in
          n_bigsteps_loop (n+1,nmax) gamespec pbspec
          (newallex, root :: allroot) cuttree
        end
    end
  end

fun n_bigsteps n gamespec pbspec ntarg target =
  let val tree = starttree_of (!decay_glob) pbspec target in
    print_endline ("Target " ^ its ntarg);
    n_bigsteps_loop (0,n) gamespec pbspec (emptyallex,[]) tree
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun random_dhtnn_gamespec gamespec =
  let
    val dimin = #dim gamespec
    val dimout = length (#movel gamespec)
    val operl = #operl gamespec
  in
    random_dhtnn (dimin,dimout) operl
  end

fun train_dhtnn gamespec (evalex,poliex) =
  let
    val _ = summary ("Eval examples: " ^ trainset_info evalex)
    val _ = summary ("Poli examples: " ^ trainset_info poliex)
    val schedule = [(100,0.1)]
    val bsize = if length evalex < 64 then 1 else 64
    val dhtnn = random_dhtnn_gamespec gamespec
    val dim = #dim gamespec
    val (etrain,ptrain) = (prepare_trainset evalex, prepare_trainset poliex)
  in
     train_dhtnn_schedule dhtnn bsize (etrain,ptrain) schedule
  end

(* -------------------------------------------------------------------------
   Results
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Adaptive difficulty
   ------------------------------------------------------------------------- *)

fun eval_targetl gamespec dhtnn targetl = 
  let
    val {opdict,headeval,headpoli,dimin,dimout} = dhtnn
    val etnn = {opdict=opdict,headnn=headeval,dimin=dimin,dimout=1}
    fun f sit = only_hd (infer_tnn etnn ((#nntm_of_sit gamespec) sit))
    val l = map_assoc f targetl
    val r = rts (average_real (map snd l))
  in
    summary ("  Average value (full dataset): " ^ r);
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
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun concat_ex ((exE,exP),(allexE,allexP)) = (exE @ allexE, exP @ allexP)

fun explore_f bstart (gamespec : ('a,''b,'c) gamespec) allex dhtnn targetl =
  let
    val pbspec =
      ((#status_of gamespec, #apply_move gamespec), 
        mk_fep_dhtnn bstart gamespec dhtnn)
    val (result,t) =
      add_time (mapi (n_bigsteps (!bigsteps_glob) gamespec pbspec)) targetl
    val (exl,allrootl) = split result
    val _ = summary ("Exploration time : " ^ rts t)
    val _ = summary_wins gamespec allrootl
  in
    foldl concat_ex allex exl
  end

fun train_f gamespec allex =
  let val (dhtnn,t) = add_time (train_dhtnn gamespec) allex in
    summary ("Training time : " ^ rts t); dhtnn
  end

fun rl_start gamespec targetl =
  let
    val _ = summary "Generation 0"
    val dhtnn = random_dhtnn_gamespec gamespec
    val targetl' = first_n (!ntarget_glob) (shuffle targetl)
    val newallex = explore_f true gamespec emptyallex dhtnn targetl'
  in
    discard_oldex newallex (!exwindow_glob)
  end

fun rl_one n gamespec targetl allex =
  let
    val _ = summary ("\nGeneration " ^ its n)
    val dhtnn = train_f gamespec allex
    val targetl' = choose_uniform gamespec dhtnn (targetl,!ntarget_glob)
    val newallex = explore_f false gamespec allex dhtnn targetl'
  in
    discard_oldex newallex (!exwindow_glob)
  end

fun rl_loop (n,nmax) gamespec targetl allex =
  if n >= nmax then allex else
    let val newallex = rl_one n gamespec targetl allex in
      rl_loop (n+1, nmax) gamespec targetl newallex
    end

fun start_rl_loop gamespec targetl =
  let 
    val _ = summary_param targetl
    val allex = rl_start gamespec targetl
  in
    rl_loop (1,!ngen_glob) gamespec targetl allex
  end


end (* struct *)

(*
app load ["rlGameArithGround","rlEnv"];
open aiLib psMCTS rlGameArithGround rlEnv;

logfile_glob := "arith_n4_test10";
ngen_glob := 40;
ntarget_glob := 100;
bigsteps_glob := 10;
nsim_glob := 1600;
tmsize_flag := true;

val allex = start_rl_loop gamespec targetl_n4;
*)


