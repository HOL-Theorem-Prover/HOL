(* ========================================================================= *)
(* FILE          : rlEnv.sml                                                 *)
(* DESCRIPTION   : Environnement for reinforcement learning                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlEnv :> rlEnv =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor";
*)

open HolKernel Abbrev boolLib aiLib psMCTS mlTreeNeuralNetwork
rlLib rlTrain

val ERR = mk_HOL_ERR "rlEnv"

type ('a,'b,'c) gamespec =
  {
  mk_startsit: 'c -> 'a psMCTS.sit,
  movel: 'b list,
  status_of : ('a psMCTS.sit -> psMCTS.status),
  apply_move : ('b -> 'a psMCTS.sit -> 'a psMCTS.sit),
  operl : (term * int) list,
  dim : int,
  nntm_of_sit: 'a psMCTS.sit -> term
  }

(* -------------------------------------------------------------------------
   Hard-coded parameters
   ------------------------------------------------------------------------- *)

val exwindow_glob = 100000
val bigsteps_glob = 50
val nsim_glob = 1600
val decay_glob = 0.99
val logfile_glob = ref "rlEnv"

(* -------------------------------------------------------------------------
   Log
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/reinforcement_learning/eval"
fun log_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end

fun summary s = log_eval (!logfile_glob) s

(* -------------------------------------------------------------------------
   Evaluation and policy
   ------------------------------------------------------------------------- *)

fun mk_fep_tnn gamespec tnn sit =
  let
    val movel = (#movel gamespec)
    val (opdict,(nn1,nn2)) = tnn
    val etnn = (opdict,nn1)
    val ptnn = (opdict,nn2)
    val nntm = (#nntm_of_sit gamespec) sit
  in
    (eval_treenn etnn nntm, combine (movel, poli_treenn ptnn nntm))
  end

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

val emptyallex = ([],[])

fun update_allex (nntm,(e,p)) (eex,pex) = ((nntm,e) :: eex, (nntm,p) :: pex)

fun update_allex_from_tree gamespec tree allex =
  let
    val root = dfind [0] tree
    val epo  = evalpoli_example tree
    val sit  = #sit root
    val nntm = (#nntm_of_sit gamespec) sit
  in
    case epo of
      NONE    => allex
    | SOME ep => update_allex (nntm,ep) allex
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
    val newtree = mcts (nsim_glob, decay_glob, true) pbspec tree
    val root = dfind [0] newtree
    val cido = select_bigstep newtree [0]
  in
    case cido of
     NONE => (allex, root :: allroot)
   | SOME cid =>
      let
        val cuttree = cut_tree newtree cid
        val newallex = update_allex_from_tree gamespec newtree allex
      in
        n_bigsteps_loop (n+1,nmax) gamespec pbspec
        (newallex, root :: allroot) cuttree
      end
  end

fun n_bigsteps n gamespec pbspec target =
  let val tree = starttree_of decay_glob pbspec target in
    n_bigsteps_loop (0,n) gamespec pbspec (emptyallex,[]) tree
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun random_dhtnn gamespec =
  let
    val polin = length (#movel gamespec)
    val operl = #operl gamespec
    val dim = #dim gamespec
  in
    (random_opdict dim operl,
    (random_headnn (dim,1), random_headnn (dim,polin)))
  end

fun train_dhtnn gamespec (evalex,poliex) =
  let
    val schedule = [(100,0.1)]
    val bsize = if length evalex < 32 then 1 else 32
    val dhtnn = random_dhtnn gamespec
    val dim = #dim gamespec
    val (etrain,ptrain) =
      (prepare_trainset_eval evalex, prepare_trainset_poli poliex)
  in
     train_dhtnn_schedule dim dhtnn bsize (etrain,ptrain) schedule
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

fun eval_targetl gamespec tnn targetl = 
  let
    val (opdict,(nn1,nn2)) = tnn
    val etnn = (opdict,nn1)
    fun f sit = eval_treenn etnn ((#nntm_of_sit gamespec) sit)
    val l = map_assoc f targetl
    val r = rts (average_real (map snd l))
  in
    summary ("  Average value (full dataset): " ^ r);
    l
  end

fun interval (step:real) (a,b) =
  if a + (step / 2.0) > b then [b] else a :: interval step (a + step,b)

fun choose_uniform gamespec tnn (targetl,ntarget) =
  let 
    val l = eval_targetl gamespec tnn targetl
    fun f r = map fst (filter (fn (_,x) => x >= r andalso x < r + 0.1) l)
    val ll = map f (interval 0.1 (0.0,0.9))
    val _ = 
      summary ("  Repartition (self-assessed): " ^ String.concatWith " " 
               (map (its o length) ll))
    fun g x = first_n (ntarget div 10) (shuffle x)
  in
    List.concat (map g ll)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun concat_ex ((exE,exP),(allexE,allexP)) = (exE @ allexE, exP @ allexP)

fun explore_f gamespec allex tnn targetl =
  let
    val pbspec =
      ((#status_of gamespec, #apply_move gamespec), mk_fep_tnn gamespec tnn)
    val (result,t) =
      add_time (map (n_bigsteps bigsteps_glob gamespec pbspec)) targetl
    val (exl,allrootl) = split result
    val _ = summary ("Exploration time : " ^ rts t)
    val _ = summary_wins gamespec allrootl
  in
    foldl concat_ex allex exl
  end

fun train_f gamespec allex =
  let
    val _ = summary ("Examples : " ^ its (length (fst allex)))
    val (tnn,t) = add_time (train_dhtnn gamespec) allex
  in
    summary ("Training time : " ^ rts t); tnn
  end

fun rl_start gamespec (targetl,ntarget) =
  let
    val _ = summary "Generation 0"
    val tnn = random_dhtnn gamespec
    val targetl' = first_n ntarget (shuffle targetl)
    val newallex = explore_f gamespec emptyallex tnn targetl'
  in
    discard_oldex newallex exwindow_glob
  end

fun rl_one n gamespec (targetl,ntarget) allex =
  let
    val _ = summary ("\nGeneration " ^ its n)
    val tnn = train_f gamespec allex
    val targetl' = choose_uniform gamespec tnn (targetl,ntarget)
    val newallex = explore_f gamespec allex tnn targetl'
  in
    discard_oldex newallex exwindow_glob
  end

fun rl_loop (n,nmax) gamespec (targetl,ntarget) allex =
  if n >= nmax then allex else
    let val newallex = rl_one n gamespec (targetl,ntarget) allex in
      rl_loop (n+1, nmax) gamespec (targetl,ntarget) newallex
    end

fun start_rl_loop (gamespec : ('a,'b,'c) gamespec) (targetl,ntarget) nmax =
  let val allex = rl_start gamespec (targetl,ntarget) in
    rl_loop (1,nmax) gamespec (targetl,ntarget) allex
  end

(*

app load ["rlGameParamod","rlEnv"];
open aiLib psMCTS rlGameParamod rlEnv;
ignorestatus_flag := true;
val maxsize = 9;
val targetl = mk_targetl maxsize 10000;
val nmax = 20;
val ntarget = 100;
logfile_glob := "paramod0";
val allex = start_rl_loop gamespec (targetl,ntarget) nmax;

*)



end (* struct *)
