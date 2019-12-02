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

fun log_in_eval obj s =
  append_endline (eval_dir ^ "/" ^ (#expname (#rl_param obj)) ^ "/log") s

fun log obj s = (log_in_eval obj s; print_endline s)

(* -------------------------------------------------------------------------
   Different representation of players
   ------------------------------------------------------------------------- *)

type splayer = (bool * dhtnn * bool * string * int)
type dplayer =
  {playerid : string, dhtnn_param : dhtnn_param, schedule : schedule}
type rplayer = (dhtnn * string)

(* -------------------------------------------------------------------------
   Parallelization of the search
   ------------------------------------------------------------------------- *)

type 'a pre_extsearch =
  {
  write_target : string -> 'a -> unit,
  read_target : string -> 'a,
  write_exl : string -> 'a rlex -> unit,
  read_exl : string -> 'a rlex,
  write_splayer : string -> splayer -> unit,
  read_splayer : string -> splayer
  }
type 'a extsearch = (splayer, 'a, bool * bool * 'a rlex) smlParallel.extspec

(* -------------------------------------------------------------------------
   Parameters of the reinforcement learning loop
   ------------------------------------------------------------------------- *)

type rl_param =
  {
  expname : string, 
  ex_window : int, 
  ncore_search : int, nsim : int, decay : real
  }

type ('a,'b,'c) rlpreobj =
  {
  rl_param : rl_param,
  max_bigsteps : 'a -> int,
  game : ('a,'b) psMCTS.game,
  pre_extsearch : 'a pre_extsearch,
  pretobdict : (string, ('a -> term) * ('c -> 'a -> term)) Redblackmap.dict,
  precomp_dhtnn : dhtnn -> 'a -> 'c,
  dplayerl : dplayer list,
  level_targetl : int -> 'a list
  }
  
type 'a rlobj =
  {
  rl_param : rl_param,
  extsearch : 'a extsearch,
  tobdict : (string, 'a -> term) Redblackmap.dict,
  dplayerl : dplayer list,
  write_exl : string -> 'a rlex -> unit,
  read_exl : string -> 'a rlex,
  board_compare : 'a * 'a -> order,
  level_targetl : int -> 'a list
  }

(* -------------------------------------------------------------------------
   Search parallelization (big steps)
   ------------------------------------------------------------------------- *)

fun mk_mcts_param noiseb nsim rlpreobj =
  {
  nsim = nsim,
  stopatwin_flag = false,
  decay = #decay (#rl_param rlpreobj),
  explo_coeff = 2.0,
  noise_all = noiseb,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real
  }

fun player_from_dhtnn game (tobc,dhtnn) ctxt board =
   let val (e,p) = infer_dhtnn dhtnn (tobc ctxt board) in
     (e, combine (#movel game,p))
   end

fun mk_bigsteps_obj rlpreobj (unib,dhtnn,noiseb,playerid,nsim) =
  let
    val game = #game rlpreobj
    val (tob,tobc) = dfind playerid (#pretobdict rlpreobj)
    fun preplayer ctxt board =
      if unib
      then uniform_player game board
      else player_from_dhtnn game (tobc,dhtnn) ctxt board
    fun precomp board = (#precomp_dhtnn rlpreobj) dhtnn board
  in
    {
    verbose = false,
    temp_flag = false,
    max_bigsteps = #max_bigsteps rlpreobj,
    precomp = precomp,
    preplayer = preplayer,
    game = game,
    mcts_param = mk_mcts_param noiseb nsim rlpreobj
    }
  end

fun extsearch_fun rlpreobj splayer target =
  let
    val obj = mk_bigsteps_obj rlpreobj splayer
    val (b1,b2,exl,_) = run_bigsteps obj target
  in
    (b1,b2,exl)
  end

fun mk_extsearch self rlpreobj =
  let
    val rl_param = #rl_param rlpreobj
    val {write_target,read_target,
         write_exl,read_exl,
         write_splayer,read_splayer} = #pre_extsearch rlpreobj
    fun write_result file (b1,b2,exl) =
      (writel (file ^ "_bstatus") [bts b1 ^ " " ^ bts b2];
       write_exl (file ^ "_exl") exl)
    fun read_result file =
      let
        val bs = only_hd (readl (file ^ "_bstatus"))
        val (b1,b2) = pair_of_list (map string_to_bool
          (String.tokens Char.isSpace bs))
        val r = (b1,b2,read_exl (file ^ "_exl"))
      in
        remove_file (file ^ "_bstatus"); r
      end
  in
    {
    self = self,
    parallel_dir = default_parallel_dir ^ "_search",
    reflect_globals = fn () => "()",
    function = extsearch_fun rlpreobj,
    write_param = write_splayer,
    read_param = read_splayer,
    write_arg = write_target,
    read_arg = read_target,
    write_result = write_result,
    read_result = read_result
    }
  end

fun mk_rlobj rlpreobj extsearch =
  {
  rl_param = #rl_param rlpreobj,
  extsearch = extsearch,
  tobdict = dmap (fst o snd) (#pretobdict rlpreobj),
  dplayerl = #dplayerl rlpreobj,
  write_exl = #write_exl (#pre_extsearch rlpreobj),
  read_exl = #read_exl (#pre_extsearch rlpreobj),
  board_compare = #board_compare (#game rlpreobj),
  level_targetl = #level_targetl rlpreobj
  }

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun rl_train rlobj exl =
  let
    val dplayerl = #dplayerl rlobj
    fun f {playerid, dhtnn_param, schedule} =
      let
        val tob = dfind playerid (#tobdict rlobj)
        val exl' = map (fn (a,b,c) => (tob a, b, c)) exl
      in
        (exl',schedule,dhtnn_param)
      end
    val argl = map f dplayerl
    val ncore = length argl
    val (dhtnnl,t) =
      add_time (parmap_queue_extern ncore mlTune.traindhtnn_extspec ()) argl;
    val rplayerl = combine (dhtnnl,map #playerid dplayerl)
  in
    log rlobj ("Training time: " ^ rts t);
    rplayerl
  end

(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

fun explore_standalone (unib,noiseb) rlobj (dhtnn,playerid) targetl =
  let
    val ncore = #ncore_search (#rl_param rlobj)
    val extspec = #extsearch rlobj
    val nsim = #nsim (#rl_param rlobj)
    val splayer = (unib,dhtnn,noiseb,playerid,nsim)
    val (l,t) = add_time (parmap_queue_extern ncore extspec splayer) targetl
    val (nwin1,nwin2) = (length (filter #1 l), length (filter #2 l))
    val exl = List.concat (map #3 l)
    val b = int_div nwin1 (length targetl) > 0.75
  in
    log rlobj ("Exploration time: " ^ rts t);
    log rlobj ("Exploration wins: " ^ its nwin1 ^ " " ^ its nwin2);
    log rlobj ("Exploration new examples: " ^ its (length exl));
    (exl,b)
  end

fun rl_explore unib rlobj level rplayer =
  let
    val rl_param = #rl_param rlobj
    val targetl = (#level_targetl rlobj) level
    val _ = log rlobj ("Exploration: " ^ its (length targetl) ^ " targets")
    val (exl,b) = explore_standalone (unib,true) rlobj rplayer targetl 
    val _ = if b then log rlobj ("Level up: " ^ its (level + 1)) else ()
  in
    (exl, if b then level + 1 else level)
  end

(* -------------------------------------------------------------------------
   Asynchronous training and exploration
   ------------------------------------------------------------------------- *)

(* helpers *)
fun wait () = OS.Process.sleep (Time.fromReal 1.0)

(* examples *)
fun ex_file rlobj n =
  eval_dir ^ "/" ^ (#expname (#rl_param rlobj)) ^ "/ex" ^ its n
fun read_one_ex rlobj n = (#read_exl rlobj) (ex_file rlobj n)
fun gather_ex rlobj acc n =
  let val ex_window = #ex_window (#rl_param rlobj) in
    if n < 0 orelse length acc > ex_window
    then first_n ex_window (rev acc) 
    else gather_ex rlobj (read_one_ex rlobj n @ acc) (n-1)
  end

fun store_ex rlobj n exl =
  (
  (#write_exl rlobj) (ex_file rlobj n) exl;
  writel_atomic (ex_file rlobj n ^ "_status") ["done"]
  )
fun retrieve_ex rlobj n = gather_ex rlobj [] n
fun exists_ex rlobj n = exists_file (ex_file rlobj n ^ "_status")
fun max_ex rlobj n =
  if not (exists_ex rlobj n) then n else max_ex rlobj (n+1)

(* player *)
fun player_file rlobj n =
  eval_dir ^ "/" ^ (#expname (#rl_param rlobj)) ^ "/player" ^ its n

fun store_player rlobj n (dhtnn,id) =
  (
  write_dhtnn (player_file rlobj n ^ "_dhtnn") dhtnn;
  writel_atomic (player_file rlobj n ^ "_id") [id]
  )
fun retrieve_player rlobj n =
  (
  read_dhtnn (player_file rlobj n ^ "_dhtnn"),   
  only_hd (readl (player_file rlobj n ^ "_id"))     
  )
fun exists_player rlobj n = exists_file (player_file rlobj n ^ "_id")
fun max_player rlobj n =
  if not (exists_player rlobj n) then n else max_player rlobj (n+1) 

(* training *)
fun rl_train_sync rlobj ((nplayer,nex),level) =
  let
    val newnex = max_ex rlobj nex
    val _ = log rlobj ("Training: player " ^ its nplayer ^ 
                       " with example " ^ its (newnex - 1))  
    val exl = retrieve_ex rlobj (newnex - 1)
    val _ = log rlobj ("Training examples: " ^ its (length exl))
    val uboardl = mk_fast_set (#board_compare rlobj) (map #1 exl)
    val _ = log rlobj ("Training unique boards: " ^ its (length uboardl))
    val rplayer = only_hd (rl_train rlobj exl)
    val _ = store_player rlobj nplayer rplayer
  in
    ((nplayer + 1, newnex),level)
  end

(* exploration *)
fun rl_explore_init rlobj level =
  let
    val _ = log rlobj ("Exploration: initialization")    
    val dplayer = only_hd (#dplayerl rlobj)
    val dhtnn = random_dhtnn (#dhtnn_param dplayer)
    val dummyplayer = (dhtnn, #playerid dplayer)
    val (newexl,_) = rl_explore true rlobj level dummyplayer
  in
    store_ex rlobj 0 newexl
  end

fun rl_explore_sync rlobj ((nplayer,nex),level) =
  let
    val newnplayer = max_player rlobj nplayer
    val _ = log rlobj ("Exploration: player " ^ 
      its (newnplayer - 1) ^ " producing example " ^ its nex)    
    val rplayer = retrieve_player rlobj (newnplayer - 1)
    val (newexl,newlevel) = rl_explore false rlobj level rplayer
  in
    store_ex rlobj nex newexl;
    ((newnplayer,nex + 1), newlevel)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun loop_sync rlobj (n,freq) arg =
  let val newarg = 
    if n mod freq = 0 
    then rl_train_sync rlobj arg
    else rl_explore_sync rlobj arg
  in  
    log rlobj ("\nGeneration " ^ its n);
    loop_sync rlobj (n+1,freq) newarg
  end

fun rl_restart_sync rlobj arg =
  let
    val expdir = eval_dir ^ "/" ^ #expname (#rl_param rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
  in
    loop_sync rlobj (0,2) arg
  end

fun rl_start_sync rlobj level =
  let 
    val expdir = eval_dir ^ "/" ^ #expname (#rl_param rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
  in
    rl_explore_init rlobj level;
    rl_restart_sync rlobj ((0,1),level)
  end


end (* struct *)
