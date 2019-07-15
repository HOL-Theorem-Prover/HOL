(* ========================================================================= *)
(* FILE          : mlReinforce.sml                                           *)
(* DESCRIPTION   : Environnement for reinforcement learning                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mlReinforce :> mlReinforce =
struct

open HolKernel Abbrev boolLib aiLib psMCTS mlTreeNeuralNetwork
smlParallel

val ERR = mk_HOL_ERR "mlReinforce"

type ('a,'b) gamespec =
  {
  movel : 'b list,
  move_compare : 'b * 'b -> order,
  string_of_move : 'b -> string,
  filter_sit : 'a -> (('b * real) list -> ('b * real) list),
  status_of : ('a -> psMCTS.status),
  apply_move : ('b -> 'a -> 'a),
  operl : (term * int) list,
  nntm_of_sit: 'a -> term,
  mk_targetl: int -> int -> 'a list,
  write_targetl: string -> 'a list -> unit,
  read_targetl: string -> 'a list,
  max_bigsteps : 'a -> int
  }

type dhex = (term * real list * real list) list
type dhtnn = mlTreeNeuralNetwork.dhtnn
type flags = bool * bool * bool
type 'a extgamespec =
  (flags * dhtnn, 'a, bool * dhex) smlParallel.extspec

(* -------------------------------------------------------------------------
   Log
   ------------------------------------------------------------------------- *)

val logfile_glob = ref "mlReinforce"
val eval_dir = HOLDIR ^ "/src/AI/machine_learning/eval"
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
val uniqex_flag = ref false
val dim_glob = ref 8
val batchsize_glob = ref 64
val nepoch_glob = ref 100
val lr_glob = ref 0.1
val ncore_train_glob = ref 4

val nsim_glob = ref 1600
val decay_glob = ref 0.99
val temp_flag = ref false
val ncore_mcts_glob = ref 8

val level_glob = ref 1
val level_threshold = ref 0.95

fun summary_param () =
  let
    val file  = "  file: " ^ (!logfile_glob)
    val para  = "parallel_dir: " ^ (!parallel_dir)
    val gen1  = "gen max: " ^ its (!ngen_glob)
    val gen2  = "target_compete: " ^ its (!ntarget_compete)
    val gen3  = "target_explore: " ^ its (!ntarget_explore)
    val gen4  = "starting level: " ^ its (!level_glob)
    val gen5  = "level threshold: " ^ rts (!level_threshold)
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
    val mcts5 = "mcts exploration coeff: " ^ rts (!exploration_coeff)
    val mcts6 = "mcts noise alpha: " ^ rts (!alpha_glob)
    val mcts7 = "mcts temp: " ^ bts (!temp_flag)
  in
    summary "Global parameters";
    summary (String.concatWith "\n  "
     ([file,para] @ 
      [gen1,gen2,gen3,gen4,gen5] @ 
      [nn0,nn1,nn2,nn3,nn4,nn6,nn5] @
      [mcts2,mcts3,mcts4,mcts5,mcts6,mcts7])
     ^ "\n")
  end

(* -------------------------------------------------------------------------
   Evaluation and policy
   ------------------------------------------------------------------------- *)

fun mk_fep_dhtnn startb gamespec dhtnn sit =
  let
    val movel = #movel gamespec
    val filter_sit = (#filter_sit gamespec) sit
    val nntm = (#nntm_of_sit gamespec) sit
  in
    if startb then (0.0, filter_sit (map (fn x => (x,1.0)) movel)) else
      let val (e,p) = infer_dhtnn dhtnn nntm in
        (e, filter_sit (combine (movel,p)))
        handle HOL_ERR _ => raise ERR "mk_fep_dhtnn"
          (its (length movel) ^ " " ^ its (length p))
      end
  end

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

val emptyallex = []

fun complete_pol gamespec mrl =
  let
    val d = dnew (#move_compare gamespec) mrl
    fun f move = dfind move d handle NotFound => 0.0
  in
    map f (#movel gamespec)
  end

fun add_rootex gamespec tree exl =
  let
    val root = dfind [] tree
    val sit  = #sit root
    val nntm = (#nntm_of_sit gamespec) sit
    val (e,p) = evalpoli_example tree
  in
    (nntm,[e], complete_pol gamespec p) :: exl
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

val verbose_flag = ref false

fun n_bigsteps_loop (n,nmax) gamespec mctsparam (exl,rootl) tree =
  if n >= nmax orelse #status_of gamespec (#sit (dfind [] tree)) <> Undecided
  then (exl,rootl) else
  let
    val sit = #sit (dfind [] tree)
    val newtree = mcts mctsparam tree
    val root = dfind [] newtree
    val filter_sit = (#filter_sit gamespec) sit
    val _ = if !verbose_flag 
            then print_endline (tts (#nntm_of_sit gamespec sit)) 
            else ()
    val movel = #movel gamespec
    val (cid,dis) = select_bigstep newtree
    val _ = if !verbose_flag
            then print_distrib (#string_of_move gamespec) dis
            else ()
    val cuttree = starttree_of mctsparam (#sit (dfind cid newtree))
                  (* cut_tree newtree cid *)
    val newexl = add_rootex gamespec newtree exl
    val newrootl = root :: rootl
  in
    n_bigsteps_loop (n+1,nmax) gamespec mctsparam (newexl,newrootl) cuttree
  end

fun n_bigsteps gamespec mctsparam target =
  let 
    val tree = starttree_of mctsparam target 
    val n = #max_bigsteps gamespec target
  in
    n_bigsteps_loop (0,n) gamespec mctsparam ([],[]) tree
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
   External parallelization specification
   ------------------------------------------------------------------------- *)

fun bstatus_to_string b = if b then "win" else "lose"
fun string_to_bstatus s = assoc s [("win",true),("lose",false)]
  handle HOL_ERR _ => raise ERR "string_to_bstatus" ""

fun string_to_bool s = 
   if s = "true" then true 
   else if s = "false" then false 
   else raise ERR "string_to_bool" ""

fun flags_to_string (b1,b2,b3) = bts b1 ^ " " ^  bts b2 ^ " " ^ bts b3
fun string_to_flags s = 
  triple_of_list (map string_to_bool (String.tokens Char.isSpace s))

fun write_param file (flags,dhtnn) =
  (writel (file ^ "_flags") [flags_to_string flags];
   write_dhtnn (file ^ "_dhtnn") dhtnn)

fun read_param file =
  ((string_to_flags o hd o readl) (file ^ "_flags"),
   read_dhtnn (file ^ "_dhtnn"))

fun write_result file (bstatus,exl) =
  (writel_atomic (file ^ "_bstatus") [bstatus_to_string bstatus];
   write_dhex (file ^ "_exl") exl)

fun read_result file =
  let
    val bstatus = (string_to_bstatus o hd o readl) (file ^ "_bstatus")
    val dhex = read_dhex (file ^ "_exl")
  in
    app remove_file [file ^ "_bstatus",file ^ "_exl"];
    (bstatus,dhex)
  end

fun reflect_globals () =
  "(" ^ String.concatWith "; "
  [
  "mlReinforce.nsim_glob := " ^ its (!nsim_glob),
  "mlReinforce.decay_glob := " ^ rts (!decay_glob),
  "mlReinforce.dim_glob := " ^ its (!dim_glob),
  "psMCTS.alpha_glob := " ^ rts (!alpha_glob),
  "psMCTS.exploration_coeff := " ^ rts (!exploration_coeff)
  ]
  ^ ")"

fun n_bigsteps_extern (gamespec: ('a,'b) gamespec) (flags,dhtnn) target =
  let
    val (noise,bstart,btemp) = flags
    val _ = temperature_flag := btemp
    val (mctsparam : ('a,'b) mctsparam) = 
      {nsim = !nsim_glob, decay = !decay_glob, noise = noise,
       status_of = #status_of gamespec,
       apply_move = #apply_move gamespec,
       fevalpoli = mk_fep_dhtnn bstart gamespec dhtnn}
    val (exl,rootl) = n_bigsteps gamespec mctsparam target
    val endroot = hd rootl
    val bstatus = #status_of gamespec (#sit endroot) = Win
  in
    (bstatus,exl)
  end

fun mk_extspec (name: string) (gamespec : ('a,'b) gamespec) =
  {
  self = name,
  reflect_globals = reflect_globals, 
  function = n_bigsteps_extern gamespec,
  write_param = write_param,
  read_param = read_param,
  write_argl = #write_targetl gamespec,
  read_argl = #read_targetl gamespec,
  write_result = write_result,
  read_result = read_result
  }

(* -------------------------------------------------------------------------
   Competition
   ------------------------------------------------------------------------- *)

fun compete_one extspec dhtnn targetl =
  let
    val flags = (false,false,false)
    val param = (flags,dhtnn)
    val ncore = !ncore_mcts_glob
    val (l,t) = add_time (parmap_queue_extern ncore extspec param) targetl
    val nwin = length (filter fst l)
  in
    summary ("Competition time : " ^ rts t); nwin
  end

fun summary_compete (w_old,w_new) =
  let val s = if w_new >= w_old then "Passed" else "Failed" in
    summary (s ^ ": " ^ its w_old ^ " " ^ its w_new)
  end

fun level_up b =
  if b then (incr level_glob; summary ("Level up: " ^ its (!level_glob)))
  else ()

fun compete (gamespec,extspec) dhtnn_old dhtnn_new =
  let
    val targetl = #mk_targetl gamespec (!level_glob) (!ntarget_compete)
    val _ = summary ("Competition targets: " ^ its (length targetl))
    val w_old = compete_one extspec dhtnn_old targetl
    val w_new = compete_one extspec dhtnn_new targetl
    val freq = int_div (Int.max (w_new,w_old)) (length targetl)
  in
    summary_compete (w_old,w_new);
    summary ("Max percentage: " ^ rts (approx 3 freq));
    level_up (freq > !level_threshold);
    if w_new >= w_old then dhtnn_new else dhtnn_old
  end

(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

fun explore startb (gamespec,extspec) allex dhtnn =
  let
    val targetl = #mk_targetl gamespec (!level_glob) (!ntarget_explore)
    val _ = summary ("Exploration targets: " ^ its (length targetl))
    val flags = (true,startb,!temp_flag)
    val param = (flags,dhtnn)
    val (l,t) = 
      add_time (parmap_queue_extern (!ncore_mcts_glob) extspec param) targetl
    val nwin = length (filter fst l)
    val exll = map snd l
    val _ = summary ("Exploration time: " ^ rts t)
    val _ = summary ("Exploration wins: " ^ its nwin)
    fun cmp ((a,_,_),(b,_,_)) = Term.compare (a,b)
    val exl1 = List.concat exll @ allex
    val exl2 = if !uniqex_flag then mk_sameorder_set cmp exl1 else exl1
    val b = int_div nwin (length targetl) > !level_threshold
  in
    level_up b; (b, first_n (!exwindow_glob) exl2)
  end

(* -------------------------------------------------------------------------
   Standalone functions for testing
   ------------------------------------------------------------------------- *)

fun mcts_test nsim gamespec dhtnn startsit =
  let
    val param = 
      {nsim = nsim, decay = 1.0, noise = false,
       status_of = #status_of gamespec,
       apply_move = #apply_move gamespec,
       fevalpoli = mk_fep_dhtnn false gamespec dhtnn}
  in
    mcts param (starttree_of param startsit)
  end

fun n_bigsteps_test gamespec dhtnn target =
  let
    val status_of = #status_of gamespec
    val mctsparam = 
      {nsim = !nsim_glob, decay = !decay_glob, noise = false,
       status_of = #status_of gamespec,
       apply_move = #apply_move gamespec,
       fevalpoli = mk_fep_dhtnn false gamespec dhtnn}
    val _ = verbose_flag := true
    val (_,rootl) = n_bigsteps gamespec mctsparam target
    val _ = verbose_flag := false
  in
    rootl
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_start (gamespec,extspec) =
  let
    val _ = remove_file (eval_dir ^ "/" ^ (!logfile_glob))
    val _ = summary_param ()
    val _ = summary "Generation 0"
    val prefile = eval_dir ^ "/" ^ (!logfile_glob) ^ "_gen" ^ its 0
    val dhtnn_random = random_dhtnn_gamespec gamespec
    val (_,allex) = explore true (gamespec,extspec) emptyallex dhtnn_random
    val dhtnn = train_f gamespec allex
  in
    write_dhtnn (prefile ^ "_dhtnn") dhtnn;
    write_dhex (prefile ^ "_allex") allex;
    (allex, dhtnn)
  end

fun rl_one n (gamespec,extspec) (allex,dhtnn) =
  let
    val prefile = eval_dir ^ "/" ^ (!logfile_glob) ^ "_gen" ^ its n
    val _ = summary ("\nGeneration " ^ its n)
    val dhtnn_new = train_f gamespec allex
    val dhtnn_best = compete (gamespec,extspec) dhtnn dhtnn_new
    val _ = write_dhtnn (prefile ^ "_dhtnn") dhtnn_best
    fun loop exl =
      let val (b,newexl) = explore false (gamespec,extspec) exl dhtnn_new in
        if b then loop newexl else newexl
      end
    val newallex = loop allex
  in
    write_dhex (prefile ^ "_allex") newallex;
    (newallex,dhtnn_best)
  end

fun rl_loop (n,nmax) (gamespec,extspec) rldata =
  if n >= nmax then rldata else
  let val rldata_new = rl_one n (gamespec,extspec) rldata in
    rl_loop (n+1, nmax) (gamespec,extspec) rldata_new
  end

fun start_rl_loop (gamespec,extspec) =
  let val (allex,dhtnn) = rl_start (gamespec,extspec) in
    rl_loop (1,!ngen_glob) (gamespec,extspec) (allex,dhtnn)
  end


end (* struct *)
