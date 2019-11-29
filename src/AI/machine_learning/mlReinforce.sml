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

type 'a level_param =
  {
  ntarget_start : int, ntarget_compete : int, ntarget_explore : int,
  level_start : int, level_threshold : real,
  level_targetl : int -> int -> 'a list
  }

type rl_param =
  {
  expname : string, ex_window : int, ex_filter : int option,
  skip_compete : bool,
  ngen : int, ncore_search : int,
  nsim_start : int , nsim_explore : int, nsim_compete : int,
  decay : real
  }

type ('a,'b,'c) rlpreobj =
  {
  rl_param : rl_param,
  level_param : 'a level_param,
  max_bigsteps : 'a -> int,
  game : ('a,'b) game,
  pre_extsearch : 'a pre_extsearch,
  pretobdict : (string, ('a -> term) * ('c -> 'a -> term)) Redblackmap.dict,
  precomp_dhtnn : dhtnn -> 'a -> 'c,
  dplayerl : dplayer list
  }

type 'a rlobj =
  {
  rl_param : rl_param,
  level_param : 'a level_param,
  extsearch : 'a extsearch,
  tobdict : (string, 'a -> term) Redblackmap.dict,
  dplayerl : dplayer list,
  write_exl : string -> 'a rlex -> unit,
  read_exl : string -> 'a rlex,
  board_compare : 'a * 'a -> order
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
  level_param = #level_param rlpreobj,
  extsearch = extsearch,
  tobdict = dmap (fst o snd) (#pretobdict rlpreobj),
  dplayerl = #dplayerl rlpreobj,
  write_exl = #write_exl (#pre_extsearch rlpreobj),
  read_exl = #read_exl (#pre_extsearch rlpreobj),
  board_compare = #board_compare (#game rlpreobj)
  }

(* -------------------------------------------------------------------------
   Logs
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/experiments/eval"

fun log_in_eval obj s =
  append_endline (eval_dir ^ "/" ^ (#expname (#rl_param obj)) ^ "/log") s

fun log obj s = (log_in_eval obj s; print_endline s)

fun log_header (obj : 'a rlobj) =
  let
    val param = #rl_param obj
    val name = "expname: " ^ (#expname param)
    val gen1 = "ngen: " ^ its (#ngen param)
    val ex0 = "ex_filter: " ^ bts (isSome (#ex_filter param))
    val ex1 = "ex_window: " ^ its (#ex_window param)
  in
    log obj "Global parameters";
    log obj (String.concatWith "\n  " ([name,gen1,ex0,ex1]) ^ "\n")
  end

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
   Competition
   ------------------------------------------------------------------------- *)

fun compete_one rlobj (dhtnn,playerid) targetl =
  let
    val ncore = #ncore_search (#rl_param rlobj)
    val extspec = #extsearch rlobj
    val splayer = (false,dhtnn,false,playerid,#nsim_compete (#rl_param rlobj))
    val (r,t) = add_time (parmap_queue_extern ncore extspec splayer) targetl
    val nwin1 = length (filter #1 r)
    val nwin2 = length (filter #2 r)
  in
    log rlobj ("Player: " ^ playerid);
    log rlobj ("Competition time : " ^ rts t);
    log rlobj ("Competition wins : " ^ its nwin1 ^ " " ^ its nwin2);
    nwin1
  end

fun rl_compete rlobj level rplayerl =
  let
    val {ntarget_start, ntarget_compete, ntarget_explore,
         level_start, level_threshold,
         level_targetl} = #level_param rlobj
    val targetl = level_targetl level ntarget_compete
    val _ = log rlobj ("Competition targets: " ^ its (length targetl))
    fun f x = compete_one rlobj x targetl
    val wl1 = map_assoc f rplayerl
    val wl1' = map snd wl1
    val bpass = exists (fn x => x >= hd wl1') (tl wl1')
    val _ = log rlobj (if bpass then "Pass" else "Fail")
    val wl2 = dict_sort compare_imax wl1
    val winner = hd wl2
    val freq = int_div (snd winner) (length targetl)
    val b = freq > level_threshold
    val newlevel = if b then level + 1 else level
    val _ = if b then log rlobj ("Level up: " ^ its newlevel) else ()
  in
    (newlevel, fst winner)
  end

(* -------------------------------------------------------------------------
   Example filtering
   ------------------------------------------------------------------------- *)

fun exclude n l =
  if n < 0 orelse null l then raise ERR "exclude" ""
  else if n = 0 then tl l
  else hd l :: exclude (n - 1) (tl l)

fun mk_filter_exll ncut exl =
  let val exll = cut_modulo ncut (shuffle exl) in
    List.tabulate (ncut, fn x => List.concat (exclude x exll))
  end

fun rl_filter_train rlobj rplayer ncut exl =
  let
    val exll = mk_filter_exll ncut exl
    val dplayerl = #dplayerl rlobj
    fun test {playerid, dhtnn_param, schedule} = playerid = snd rplayer
    val {playerid, dhtnn_param, schedule} = valOf (List.find test dplayerl)
    fun f l =
      let
        val tob = dfind playerid (#tobdict rlobj)
        val l' = map (fn (a,b,c) => (tob a, b, c)) l
      in
        (l',schedule, dhtnn_param)
      end
    val argl = map f exll
    val ncore = length argl
    val (dhtnnl,t) =
      add_time (parmap_queue_extern ncore mlTune.traindhtnn_extspec ()) argl;
    val rplayerl = map (fn x => (x,playerid)) dhtnnl
  in
    log rlobj ("Filter training time : " ^ rts t);
    combine (exll,rplayerl)
  end

fun rl_filter_compete rlobj level explayerl =
  let
    val {ntarget_start, ntarget_compete, ntarget_explore,
         level_start, level_threshold,
         level_targetl} = #level_param rlobj
    val targetl = level_targetl level ntarget_compete
    val _ = log rlobj ("Filter competition targets: " ^ its (length targetl))
    fun f x = compete_one rlobj (snd x) targetl
    val wl1 = map_assoc f explayerl
    val wl2 = dict_sort compare_imax wl1
    val winnerexl = fst (fst (hd wl2))
  in
    log rlobj ("Filter examples: " ^ its (length winnerexl));
    winnerexl
  end

fun rl_filter rlobj rplayer ncut level exl =
  let val explayerl = rl_filter_train rlobj rplayer ncut exl in
    rl_filter_compete rlobj level explayerl
  end

(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

fun explore_one rlobj unib (dhtnn,playerid) targetl =
  let
    val ncore = #ncore_search (#rl_param rlobj)
    val extspec = #extsearch rlobj
    val nsim =
      if unib
      then #nsim_start (#rl_param rlobj)
      else #nsim_explore (#rl_param rlobj)
    val splayer = (unib,dhtnn,true,playerid,nsim)
    val (l,t) = add_time (parmap_queue_extern ncore extspec splayer) targetl
    val nwin1 = length (filter #1 l)
    val nwin2 = length (filter #2 l)
    val exl = List.concat (map #3 l)
  in
    log rlobj ("Exploration time: " ^ rts t);
    log rlobj ("Exploration wins: " ^ its nwin1 ^ " " ^ its nwin2);
    log rlobj ("Exploration new examples: " ^ its (length exl));
    (nwin1,exl)
  end

fun rl_explore rlobj level unib rplayer =
  let
    val rl_param = #rl_param rlobj
    val {ntarget_start, ntarget_compete, ntarget_explore,
         level_start, level_threshold,
         level_targetl} = #level_param rlobj
    val ntarget = if unib then ntarget_start else ntarget_explore
    val targetl = level_targetl level ntarget
    val _ = log rlobj ("Exploration: " ^ its (length targetl) ^ " targets")
    val (nwin,exl1) = explore_one rlobj unib rplayer targetl 
    (*
    val ex_filter = #ex_filter rl_param
    val ex_window = #ex_window rl_param
    val exl2 = exl1 @ exl
    val _ = log rlobj ("Exploration examples: " ^ its (length exl2))
    val exl3 =
      if length exl2 > ex_window then
        if isSome ex_filter
        then rl_filter rlobj rplayer (valOf ex_filter) level exl2
        else first_n ex_window exl2
      else exl2
    val uboardl = mk_fast_set (#board_compare rlobj) (map #1 exl2)
    val _ = log rlobj ("unique boards: " ^ its (length uboardl))
    *)
    val b = int_div nwin (length targetl) > level_threshold
    val newlevel = if b then level + 1 else level
  in
    if b then log rlobj ("Level up: " ^ its newlevel) else ();
    (exl1,newlevel)
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
fun rl_train_async rlobj (nplayer,nex) =
  let val newnex = max_ex rlobj nex in 
    if newnex = nex then (wait (); rl_train_async rlobj (nplayer,nex)) else
    let
      val _ = log rlobj ("Training: player " ^ its nplayer ^ 
                         " with example " ^ its (newnex - 1))  
      val exl = retrieve_ex rlobj (newnex - 1)
      val _ = log rlobj ("Training examples: " ^ its (length exl))
      val uboardl = mk_fast_set (#board_compare rlobj) (map #1 exl)
      val _ = log rlobj ("Training unique boards: " ^ its (length uboardl))
      val rplayer = only_hd (rl_train rlobj exl)
      val _ = store_player rlobj nplayer rplayer
    in
      rl_train_async rlobj (nplayer + 1, newnex) 
    end
 end

(* exploration *)
fun rl_explore_async rlobj (nplayer,nex) level =
  let
    val newnplayer = max_player rlobj nplayer
    val _ = log rlobj ("Exploration: player " ^ 
      its (newnplayer - 1) ^ " producing example " ^ its nex)    
    val rplayer = retrieve_player rlobj (newnplayer - 1)
    val (newexl,newlevel) = rl_explore rlobj level false rplayer
    val _ = store_ex rlobj nex newexl
  in
    rl_explore_async rlobj (newnplayer,nex + 1) newlevel
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun execute (f: unit -> unit) = f ()
fun parmap_fun fl = ignore (parmap_exact (length fl) execute fl)

fun rl_restart_async rlobj (nplayer,nex) level =
  let  
    val expdir = eval_dir ^ "/" ^ #expname (#rl_param rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
  in
    parmap_fun 
      [fn () => rl_train_async rlobj (nplayer,nex),
       fn () => rl_explore_async rlobj (nplayer,nex) level]
  end

fun rl_start_async rlobj level =
  let 
    val expdir = eval_dir ^ "/" ^ #expname (#rl_param rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
    val dplayer = only_hd (#dplayerl rlobj)
    val dhtnn = random_dhtnn (#dhtnn_param dplayer)
  in
    store_player rlobj 0 (dhtnn, #playerid dplayer);
    rl_restart_async rlobj (1,0) level
  end

end (* struct *)
