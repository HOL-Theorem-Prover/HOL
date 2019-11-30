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
type 'a leveld = ('a, int * bool list * int) Redblackmap.dict

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
  write_boardl : string -> 'a list -> unit,
  read_boardl : string -> 'a list
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
  write_boardl : string -> 'a list -> unit,
  read_boardl : string -> 'a list
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
  write_boardl = #write_boardl rlpreobj,
  read_boardl = #read_boardl rlpreobj
  }

(* -------------------------------------------------------------------------
   Levels
   ------------------------------------------------------------------------- *)

fun compare_target ((_,(ord1,_,wait1)),(_,(ord2,_,wait2))) =
  cpl_compare Int.compare Int.compare ((wait1,ord1),(wait2,ord2))

fun n_true bstatusl = case bstatusl of
    true :: m => 1 + n_true m
  | _ => 0

fun n_false bstatusl = case bstatusl of
    false :: m => 1 + n_true m
  | _ => 0

fun difficulty (target,(_,bstatusl,_)) = 
  case (n_true bstatusl, n_false bstatusl) of
    (0,0) => 0
  | (x,0) => x
  | (0,x) => ~x
  | _ => raise ERR "difficulty" ""

fun update_leveld_one ((target,bstatus),leveld) =
  let 
    val (ord1,bstatusl,wait) = dfind target leveld 
      handle NotFound => raise ERR "update_leveld_one" ""
    val newbstatusl = bstatus :: bstatusl
    val newwait = Int.max (n_true bstatusl, n_false bstatusl)
  in
    dadd target (ord1,newbstatusl,newwait) leveld
  end

fun decrease_wait (_,(a,b,wait)) = (a,b,if wait <= 0 then 0 else wait - 1)

fun update_leveld leveld targetbl =
  dmap decrease_wait (foldl update_leveld_one leveld targetbl)

fun level_targetl leveld =
  let
    val targetl1 = first_n 400 (dict_sort compare_target (dlist leveld))
    val targetl2 = map_assoc difficulty targetl1
  in
    map (fst o fst) (dict_sort compare_imin targetl2)
  end

fun stats_leveld rlobj leveld =
  let
    val l = map snd (map_assoc difficulty (dlist leveld))
    val r0 = filter (fn x => x <= ~2) l
    val r1 = filter (fn x => x <= ~1) l
    val r2 = filter (fn x => x = 0) l
    val r3 = filter (fn x => x >= 1) l
    val r4 = filter (fn x => x >= 2) l
  in 
    log rlobj ("Exploration: level_geq1 " ^ (its (length r3)));
    log rlobj ("Exploration: difficulty_distrib " 
      ^ String.concatWith " " (map (its o length) [r4,r3,r2,r1,r0]))
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
   Exploration
   ------------------------------------------------------------------------- *)

fun explore_one rlobj (dhtnn,playerid) targetl =
  let
    val ncore = #ncore_search (#rl_param rlobj)
    val extspec = #extsearch rlobj
    val nsim = #nsim (#rl_param rlobj)
    val splayer = (false,dhtnn,true,playerid,nsim)
    val (l,t) = add_time (parmap_queue_extern ncore extspec splayer) targetl
    val nwin1 = length (filter #1 l)
    val nwin2 = length (filter #2 l)
    fun f (b,_,locexl) = (#1 (last locexl),b) 
    val targetbl = map f l
    val exl = List.concat (map #3 l)
  in
    log rlobj ("Exploration time: " ^ rts t);
    log rlobj ("Exploration wins: " ^ its nwin1 ^ " " ^ its nwin2);
    log rlobj ("Exploration new examples: " ^ its (length exl));
    (nwin1,exl,targetbl)
  end

fun rl_explore rlobj leveld rplayer =
  let
    val rl_param = #rl_param rlobj
    val targetl = level_targetl leveld
    val _ = log rlobj ("Exploration: " ^ its (length targetl) ^ " targets")
    val (nwin,exl,targetbl) = explore_one rlobj rplayer targetl 
  in
    (exl, update_leveld leveld targetbl)
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

(* levels *)
fun leveld_file rlobj n =
  eval_dir ^ "/" ^ (#expname (#rl_param rlobj)) ^ "/leveld" ^ its n

fun string_of_bstatusl bstatusl =
  String.concatWith " " (map bts bstatusl)
fun bstatusl_of_string s =
  map string_to_bool (String.tokens Char.isSpace s)

fun store_leveld rlobj n leveld =
  let 
    val file = leveld_file rlobj n
    val (l1,l2) = split (dlist leveld) 
    val (l2a,l2b,l2c) = split_triple l2
  in 
    (#write_boardl rlobj) file l1;
    writel (file ^ "_ord") (map its l2a);
    writel (file ^ "_bstatusl") (map string_of_bstatusl l2b);
    writel (file ^ "_wait") (map its l2c)
  end

fun retrieve_leveld rlobj n =
  let 
    val file = leveld_file rlobj n
    val boardl = (#read_boardl rlobj) file
    val ordl = map string_to_int (readl (file ^ "_ord"))
    val bstatusl = map bstatusl_of_string (readl (file ^ "_bstatusl"))
    val waitl = map string_to_int (readl (file ^ "_wait"))
  in 
    dnew (#board_compare rlobj) 
      (combine (boardl, combine_triple (ordl,bstatusl,waitl)))
  end

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
fun rl_explore_async rlobj (nplayer,nex) leveld =
  let
    val newnplayer = max_player rlobj nplayer
    val _ = log rlobj ("Exploration: player " ^ 
      its (newnplayer - 1) ^ " producing example " ^ its nex)    
    val rplayer = retrieve_player rlobj (newnplayer - 1)
    val (newexl,newleveld) = rl_explore rlobj leveld rplayer
    val _ = store_ex rlobj nex newexl
    val _ = store_leveld rlobj nex newleveld
    val _ = stats_leveld rlobj newleveld
  in
    rl_explore_async rlobj (newnplayer,nex + 1) newleveld
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun execute (f: unit -> unit) = f ()
fun parmap_fun fl = ignore (parmap_exact (length fl) execute fl)

fun rl_restart_async rlobj (nplayer,nex) leveld =
  let
    val expdir = eval_dir ^ "/" ^ #expname (#rl_param rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
  in
    parmap_fun
      [fn () => rl_train_async rlobj (nplayer,nex),
       fn () => rl_explore_async rlobj (nplayer,nex) leveld]
  end

fun rl_start_async rlobj leveld =
  let 
    val expdir = eval_dir ^ "/" ^ #expname (#rl_param rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
    val dplayer = only_hd (#dplayerl rlobj)
    val dhtnn = random_dhtnn (#dhtnn_param dplayer)
  in
    store_player rlobj 0 (dhtnn, #playerid dplayer);
    rl_restart_async rlobj (1,0) leveld
  end

end (* struct *)
