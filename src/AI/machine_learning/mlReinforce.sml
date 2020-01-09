(* ========================================================================= *)
(* FILE          : mlReinforce.sml                                           *)
(* DESCRIPTION   : Environnement for reinforcement learning                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mlReinforce :> mlReinforce =
struct

open HolKernel Abbrev boolLib aiLib psMCTS psBigSteps
  mlNeuralNetwork mlTreeNeuralNetwork smlParallel

val ERR = mk_HOL_ERR "mlReinforce"

(* -------------------------------------------------------------------------
   Logs
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/experiments/eval"
fun log_in_eval rlobj s =
  append_endline (eval_dir ^ "/" ^ (#expname (#rlparam rlobj)) ^ "/log") s
fun log rlobj s = (log_in_eval rlobj s; print_endline s)

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type 'a gameio =
  {write_boardl : string -> 'a list -> unit,
   read_boardl : string -> 'a list}
type splayer = bool * tnn * bool * int
type 'a dplayer = 
  {tob : 'a -> term list, schedule : schedule, tnnparam : tnnparam}
type 'a es = (splayer, 'a, bool * 'a rlex) smlParallel.extspec
type rlparam =
  {expname : string, exwindow : int, ncore : int, nsim : int, decay : real}
type ('a,'b) rlobj =
  {
  rlparam : rlparam,
  game : ('a,'b) psMCTS.game,
  gameio : 'a gameio,
  level_targetl : int -> 'a list,
  dplayer : 'a dplayer
  }

(* -------------------------------------------------------------------------
   Big steps
   ------------------------------------------------------------------------- *)

fun mk_mctsparam noiseb nsim rlobj =
  {
  nsim = nsim,
  stopatwin_flag = false,
  decay = #decay (#rlparam rlobj),
  explo_coeff = 2.0,
  noise_all = noiseb,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = true, avoidlose = true
  }

fun player_from_tnn tnn tob game board =
  let 
    val movel = (#available_movel game) board
    val rll = map snd (infer_tnn tnn (tob board)) 
    val _ = if null rll then raise ERR "player_from_tnn" "" else ()
  in
    (
    singleton_of_list (hd rll), 
    combine (movel, map singleton_of_list (tl rll))
    )
  end

fun mk_bsobj rlobj (unib,tnn,noiseb,nsim) =
  let
    val game = #game rlobj
    val tob = #tob (#dplayer rlobj)
    fun player board = player_from_tnn tnn tob game board
  in
    {
    verbose = false, temp_flag = false,
    player = player, game = game,
    mctsparam = mk_mctsparam noiseb nsim rlobj
    }
  end

(* -------------------------------------------------------------------------
   I/O for external parallelization
   ------------------------------------------------------------------------- *)

fun write_rlex gameio file rlex =
  let val (boardl,rll) = split rlex in 
    (#write_boardl gameio) (file ^ "_boardl") boardl;
    writel (file ^ "_rll") (map reall_to_string rll)
  end

fun read_rlex gameio file =
  let
    val boardl = (#read_boardl gameio) (file ^ "_boardl")
    val rll = map string_to_reall (readl (file ^ "_rll"))
  in
    combine (boardl,rll)
  end

fun write_splayer file (unib,tnn,noiseb,nsim) =
  (
  write_tnn (file ^ "_tnn") tnn;
  writel (file ^ "_flags") [String.concatWith " " (map bts [unib,noiseb])];
  writel (file ^ "_nsim") [its nsim]
  )

fun read_splayer file =
  let
    val tnn = read_tnn (file ^ "_tnn")
    val (unib,noiseb) =
      pair_of_list (map string_to_bool
        (String.tokens Char.isSpace 
           (singleton_of_list (readl (file ^ "_flags")))))
    val nsim = string_to_int (singleton_of_list (readl (file ^ "_nsim")))
  in
    (unib,tnn,noiseb,nsim)
  end

fun write_result gameio file (b,rlex) =
  (
  writel (file ^ "_bstatus") [bts b];
  write_rlex gameio (file ^ "_rlex") rlex
  )

fun read_result gameio file =
  let val s = singleton_of_list (readl (file ^ "_bstatus")) in
    (string_to_bool s, read_rlex gameio (file ^ "_rlex"))
  end

fun write_target gameio file target = 
  (#write_boardl gameio) (file ^ "_target") [target]

fun read_target gameio file = 
  singleton_of_list ((#read_boardl gameio) (file ^ "_target"))

(* -------------------------------------------------------------------------
   I/O for storage and restart
   ------------------------------------------------------------------------- *)

fun rlex_file rlobj n =
  eval_dir ^ "/" ^ (#expname (#rlparam rlobj)) ^ "/rlex" ^ its n
fun store_rlex rlobj n rlex =
  write_rlex (#gameio rlobj) (rlex_file rlobj n) rlex
fun gather_ex rlobj acc n =
  let 
    val exwindow = #exwindow (#rlparam rlobj) 
    fun read_ex () = read_rlex (#gameio rlobj) (rlex_file rlobj n)
  in
    if n < 0 orelse length acc > exwindow
    then first_n exwindow (rev acc) 
    else gather_ex rlobj (read_ex () @ acc) (n-1)
  end
fun retrieve_rlex rlobj n = gather_ex rlobj [] n

fun tnn_file rlobj n =
  eval_dir ^ "/" ^ (#expname (#rlparam rlobj)) ^ "/tnn" ^ its n
fun store_tnn rlobj n tnn = write_tnn (tnn_file rlobj n) tnn
fun retrieve_tnn rlobj n = read_tnn (tnn_file rlobj n)

(* -------------------------------------------------------------------------
   External parallelization
   ------------------------------------------------------------------------- *)

fun extsearch_fun rlobj splayer target =
  let
    val bsobj = mk_bsobj rlobj splayer
    val (b1,rlex,_) = run_bigsteps bsobj target
  in
    (b1,rlex)
  end

fun mk_extsearch self (rlobj as {rlparam,gameio,...}) =
  {
  self = self,
  parallel_dir = default_parallel_dir ^ "_search",
  reflect_globals = fn () => "()",
  function = extsearch_fun rlobj,
  write_param = write_splayer,
  read_param = read_splayer,
  write_arg = write_target gameio,
  read_arg = read_target gameio,
  write_result = write_result gameio,
  read_result = read_result gameio
  }

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun rl_train ngen rlobj rlex =
  let
    val {tob,schedule,tnnparam} = #dplayer rlobj
    fun f (a,b) = combine (tob a, map (fn x => [x]) b)
    val tnnex = map f rlex
    val uex = mk_fast_set (list_compare Term.compare) (map (tob o fst) rlex)
    val _ = log rlobj ("Training examples: " ^ its (length rlex))
    val _ = log rlobj ("Training unique  : " ^ its (length uex))
    val randtnn = random_tnn tnnparam
    val (tnn,t) = add_time (train_tnn schedule randtnn) (tnnex,[])
  in
    log rlobj ("Training time: " ^ rts t); 
    store_tnn rlobj ngen tnn;
    tnn
  end

(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

fun rl_explore_targetl (unib,noiseb) (rlobj,es) tnn targetl =
  let
    val ncore = #ncore (#rlparam rlobj)
    val nsim = #nsim (#rlparam rlobj)
    val splayer = (unib,tnn,noiseb,nsim)
    val (l,t) = add_time (parmap_queue_extern ncore es splayer) targetl
    val nwin = length (filter fst l)
    val rlex = List.concat (map snd l)
    val rlex2 = filter (fn (_,x) => length x = 2) rlex
    val rlex1 = filter (fn (_,x) => length x = 1) rlex
    val b = int_div nwin (length targetl) > 0.75
  in
    log rlobj ("Exploration time: " ^ rts t);
    log rlobj ("Exploration wins: " ^ its nwin);
    log rlobj ("Exploration new examples: " ^ its (length rlex) ^ 
      its (length rlex1) ^ its (length rlex2));
    (rlex,b)
  end

fun rl_compete_targetl unib (rlobj,es) tnn targetl =
  rl_explore_targetl (unib,false) (rlobj,es) tnn targetl

fun rl_explore_level unib (rlobj,es) (tnn,level) =
  let
    val rlparam = #rlparam rlobj
    val (targetl,t) = add_time (#level_targetl rlobj) level
    val _ = log rlobj ("Exploration: " ^ its (length targetl) ^ 
      " targets generated in " ^ rts t ^ " seconds")
    val (rlex,b) = rl_explore_targetl (unib,true) (rlobj,es) tnn targetl 
    val _ = if (b andalso not unib)
      then log rlobj ("Level up: " ^ its (level + 1)) else ()
  in
    (rlex, if (b andalso not unib) then level + 1 else level)
  end

fun rl_explore_init ngen (rlobj,es) level =
  let
    val _ = log rlobj "Exploration: initialization"  
    val dummy = random_tnn (#tnnparam (#dplayer rlobj))
    val (rlex,_) = rl_explore_level true (rlobj,es) (dummy,level)
  in
    store_rlex rlobj ngen rlex; rlex
  end

fun rl_explore_cont ngen (rlobj,es) (tnn,rlex,level) =
  let 
    val (rlex1,newlevel) = rl_explore_level false (rlobj,es) (tnn,level) 
    val rlex2 = first_n (#exwindow (#rlparam rlobj)) (rlex1 @ rlex)
  in
    store_rlex rlobj ngen rlex1;
    (rlex2, newlevel)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_loop ngen (rlobj,es) (rlex,level) =
  let 
    val _ = log rlobj ("\nGeneration " ^ its ngen)
    val tnn = rl_train ngen rlobj rlex
    val (newrlex,newlevel) = rl_explore_cont ngen (rlobj,es) (tnn,rlex,level)
  in
    rl_loop (ngen + 1) (rlobj,es) (newrlex,newlevel)
  end   

fun rl_start (rlobj,es) level =
  let 
    val expdir = eval_dir ^ "/" ^ #expname (#rlparam rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
    val rlex = rl_explore_init 0 (rlobj,es) level
  in
    rl_loop 1 (rlobj,es) (rlex,level)
  end

fun rl_restart ngen (rlobj,es) level =
  let 
    val expdir = eval_dir ^ "/" ^ #expname (#rlparam rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
    val rlex = retrieve_rlex rlobj ngen
  in
    rl_loop (ngen + 1) (rlobj,es) (rlex,level)
  end

end (* struct *)
