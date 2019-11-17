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
type 'a extsearch = (splayer, 'a, bool * 'a rlex) smlParallel.extspec

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
  ngen : int, ncore_search : int,
  nsim_start : int , nsim_explore : int, nsim_compete : int,
  decay : real
  }

type ('a,'b) rlpreobj =
  {
  rl_param : rl_param,
  level_param : 'a level_param,
  max_bigsteps : 'a -> int,
  game : ('a,'b) game,
  pre_extsearch : 'a pre_extsearch,
  tobdict : (string, 'a -> term) Redblackmap.dict,
  dplayerl : dplayer list
  }

type 'a rlobj =
  {
  rl_param : rl_param,
  level_param : 'a level_param,
  extsearch : 'a extsearch,
  tobdict : (string,'a -> term) Redblackmap.dict,
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
  noise_flag = noiseb,
  noise_coeff = 0.25,
  noise_alpha = 0.2
  }

fun player_from_dhtnn game (tob,dhtnn) board =
   let val (e,p) = infer_dhtnn dhtnn (tob board) in
     (e, combine (#movel game,p))
   end

fun mk_bigsteps_obj rlpreobj (unib,dhtnn,noiseb,playerid,nsim) =
  let
    val tob = dfind playerid (#tobdict rlpreobj)
    val game = #game rlpreobj
    val player = if unib then uniform_player game
      else player_from_dhtnn game (tob,dhtnn)
  in
    {
    verbose = false,
    temp_flag = false,
    max_bigsteps = #max_bigsteps rlpreobj,
    mcts_obj =
       {mcts_param = mk_mcts_param noiseb nsim rlpreobj,
        game = #game rlpreobj,
        player = player}
    }
  end

fun extsearch_fun rlpreobj splayer target =
  let
    val obj = mk_bigsteps_obj rlpreobj splayer
    val (bstatus,exl,_) = run_bigsteps obj target
  in
    (bstatus,exl)
  end

fun mk_extsearch self rlpreobj =
  let
    val rl_param = #rl_param rlpreobj
    val {write_target,read_target,
         write_exl,read_exl,
         write_splayer,read_splayer} = #pre_extsearch rlpreobj
    fun write_result file (b,exl) =
      (writel (file ^ "_bstatus") [bts b];
       write_exl (file ^ "_exl") exl)
    fun read_result file =
      let val r =
        (string_to_bool (only_hd (readl (file ^ "_bstatus"))),
         read_exl (file ^ "_exl"))
      in
        remove_file (file ^ "_bstatus"); r
      end
  in
    {
    self = self,
    parallel_dir = default_parallel_dir ^ "__" ^ #expname rl_param,
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
  tobdict = #tobdict rlpreobj,
  dplayerl = #dplayerl rlpreobj,
  write_exl = #write_exl (#pre_extsearch rlpreobj),
  read_exl = #read_exl (#pre_extsearch rlpreobj),
  board_compare = #board_compare (#game rlpreobj)
  }

(* -------------------------------------------------------------------------
   Logs
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/experiments/eval"

fun log_in_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end

fun log obj s = (log_in_eval (#expname (#rl_param obj)) s; print_endline s)

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
    log rlobj ("Total training time : " ^ rts t);
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
    val nwin = length (filter fst r)
  in
    log rlobj ("Player: " ^ playerid);
    log rlobj ("Competition time : " ^ rts t);
    log rlobj ("Competition wins : " ^ its nwin);
    nwin
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
    val nwin = length (filter fst l)
    val exl = List.concat (map snd l)
  in
    log rlobj ("Exploration time: " ^ rts t);
    log rlobj ("Exploration wins: " ^ its nwin);
    log rlobj ("Exploration new examples: " ^ its (length exl));
    (nwin,exl)
  end

fun rl_explore ngen rlobj level unib rplayer exl =
  let
    val rl_param = #rl_param rlobj
    val {ntarget_start, ntarget_compete, ntarget_explore,
         level_start, level_threshold,
         level_targetl} = #level_param rlobj
    val ntarget = if unib then ntarget_start else ntarget_explore
    val targetl = level_targetl level ntarget
    val _ = log rlobj ("Exploration: " ^ its (length targetl) ^ " targets")
    val (nwin,exl1) = explore_one rlobj unib rplayer targetl
    val expname = #expname (#rl_param rlobj)
    val file = eval_dir ^ "/" ^ expname ^
      "examples_gen" ^ its ngen ^ "_level" ^ its level
    val _ = (#write_exl rlobj) file exl1
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
    val b = int_div nwin (length targetl) > level_threshold
    val newlevel = if b then level + 1 else level
  in
    if b then log rlobj ("Level up: " ^ its newlevel) else ();
    (b,exl3,newlevel)
  end

fun loop_rl_explore ngen rlobj level unib rplayer exl =
  let val (b,newexl,newlevel) = rl_explore ngen rlobj level unib rplayer exl in
    if b
    then loop_rl_explore ngen rlobj newlevel unib rplayer newexl
    else (newexl,newlevel)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_init rlobj =
  let
    val expname = #expname (#rl_param rlobj)
    val level = #level_start (#level_param rlobj)
    val _ = remove_file (eval_dir ^ "/" ^ expname)
    val _ = log_header rlobj
    val _ = log rlobj "\nGeneration 0"
    val file = eval_dir ^ "/" ^ expname ^ "_gen0"
    val dplayer = hd (#dplayerl rlobj)
    val dhtnn = random_dhtnn (#dhtnn_param dplayer)
    val dummyrplayer = (dhtnn, #playerid dplayer)
    val (allex,newlevel) = loop_rl_explore 0 rlobj level true dummyrplayer []
  in
    (allex,NONE,newlevel)
  end

fun rl_one n rlobj (allex,rplayero,level) =
  let
    val expname = #expname (#rl_param rlobj)
    val file = eval_dir ^ "/" ^ expname ^ "_gen" ^ its n
    val _ = log rlobj ("\nGeneration " ^ its n)
    val rplayerl = rl_train rlobj allex
    val rplayero' = if isSome rplayero then [valOf rplayero] else []
    val (level1,rplayer_best) =
      rl_compete rlobj level (rplayero' @ rplayerl)
    val _ = write_dhtnn (file ^ "_dhtnn") (fst rplayer_best)
    val _ = writel (file ^ "_playerid") [snd rplayer_best]
    val (newallex,level2) = loop_rl_explore n rlobj level1 false
      rplayer_best allex
  in
    (newallex,SOME rplayer_best,level2)
  end

fun cont_rl_loop rlobj i rldata =
  if i > #ngen (#rl_param rlobj) then rldata else
  let val rldata_new = rl_one i rlobj rldata in
    cont_rl_loop rlobj (i+1) rldata_new
  end

fun start_rl_loop rlobj = cont_rl_loop rlobj 1 (rl_init rlobj)

end (* struct *)
