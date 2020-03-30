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

val eval_dir = HOLDIR ^ "/examples/AI_tasks/eval"
fun log_in_eval rlobj s =
  append_endline (eval_dir ^ "/" ^ (#expname (#rlparam rlobj)) ^ "/log") s
fun log rlobj s = (log_in_eval rlobj s; print_endline s)

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type 'a targetd = ('a, bool list) Redblackmap.dict
type 'a gameio =
  {write_boardl : string -> 'a list -> unit, read_boardl : string -> 'a list}
type splayer = 
  {unib : bool, tnn : tnn, noiseb : bool, nsim : int}
type 'a dplayer =
  {pretob : ('a * tnn) option -> 'a -> term list,
   schedule : schedule, tnnparam : tnnparam}
type 'a es = (splayer, 'a, bool * 'a rlex) smlParallel.extspec
type rlparam =
  {expname : string, exwindow : int, ncore : int,
   ntarget : int, nsim : int, decay : real}
type ('a,'b) rlobj =
  {
  rlparam : rlparam,
  game : ('a,'b) psMCTS.game,
  gameio : 'a gameio,
  dplayer : 'a dplayer
  }

(* -------------------------------------------------------------------------
   Big steps
   ------------------------------------------------------------------------- *)

fun mk_mctsparam splayer rlobj =
  {
  timer = NONE, nsim = SOME (#nsim splayer), stopatwin_flag = false,
  decay = #decay (#rlparam rlobj), explo_coeff = 2.0,
  noise_all = false, noise_root = (#noiseb splayer),
  noise_coeff = 0.25, noise_gen = random_real,
  noconfl = false, avoidlose = false,
  eval_endstate = true (* todo : reflect this parameter in rlparam *)
  }

fun player_from_tnn tnn tob game board =
  let
    val amovel = (#available_movel game) board
    val (e,p) = pair_of_list (map snd (infer_tnn tnn (tob board)))
    val d = dnew (#move_compare game) (combine (#movel game,p))
    fun f x = dfind x d handle NotFound => raise ERR "player_from_tnn" ""
  in
    (singleton_of_list e, map_assoc f amovel)
  end

fun mk_bsobj rlobj (splayer as {unib,tnn,noiseb,nsim}) =
  let
    val game = #game rlobj
    val pretob = #pretob (#dplayer rlobj)
    fun preplayer target =
      let val tob = pretob (SOME (target,tnn)) in
        fn board => player_from_tnn tnn tob game board
      end
    fun random_preplayer target board = random_player game board
  in
    {
    verbose = false, temp_flag = false,
    preplayer = if unib then random_preplayer else preplayer,
    game = game,
    mctsparam = mk_mctsparam splayer rlobj
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

fun write_splayer file {unib,tnn,noiseb,nsim} =
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
    {unib=unib,tnn=tnn,noiseb=noiseb,nsim=nsim}
  end

fun write_result gameio file (b,rlex) =
  (writel (file ^ "_bstatus") [bts b];
   write_rlex gameio (file ^ "_rlex") rlex)

fun read_result gameio file =
  (string_to_bool (singleton_of_list (readl (file ^ "_bstatus"))), 
   read_rlex gameio (file ^ "_rlex"))

fun write_target gameio file target =
  (#write_boardl gameio) (file ^ "_target") [target]
  handle Subscript => raise ERR "write_target" ""

fun read_target gameio file =
  singleton_of_list ((#read_boardl gameio) (file ^ "_target"))

(* -------------------------------------------------------------------------
   I/O for storage and restart
   ------------------------------------------------------------------------- *)

(* Example *)
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

(* TNN *)
fun tnn_file rlobj n =
  eval_dir ^ "/" ^ (#expname (#rlparam rlobj)) ^ "/tnn" ^ its n
fun store_tnn rlobj n tnn = write_tnn (tnn_file rlobj n) tnn
fun retrieve_tnn rlobj n = read_tnn (tnn_file rlobj n)

(* Target *)
fun targetd_file rlobj n =
  eval_dir ^ "/" ^ (#expname (#rlparam rlobj)) ^ "/targetd" ^ its n

fun blts bl = String.concatWith " " (map bts bl)
fun stbl s = map string_to_bool (String.tokens Char.isSpace s)

fun store_targetd rlobj n targetd =
  let 
    val file = targetd_file rlobj n
    val (l1,l2) = split (dlist targetd) 
  in
    #write_boardl (#gameio rlobj) (file ^ "_boardl") l1;
    writel (file ^ "_bl") (map blts l2)
  end

fun retrieve_targetd rlobj n =
  let
    val file = targetd_file rlobj n
    val l1 = #read_boardl (#gameio rlobj) (file ^ "_boardl")
    val l2 = map stbl (readl (file ^ "_bl"))
  in
    dnew (#board_compare (#game rlobj)) (combine (l1,l2))
  end

(* -------------------------------------------------------------------------
   External parallelization
   ------------------------------------------------------------------------- *)

fun extsearch_fun rlobj splayer target =
  let
    val bsobj = mk_bsobj rlobj splayer
    val (b1, rlex, _) = run_bigsteps bsobj target
  in
    ((b1, rlex) : bool * 'a rlex)
  end
  handle Subscript => raise ERR "extsearch_fun" "subscript"

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
    val {pretob,schedule,tnnparam} = #dplayer rlobj
    fun tob board = pretob NONE board
    fun f (a,b) = combine (tob a,[[hd b],tl b])
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
    val {ncore,nsim,...} = #rlparam rlobj
    val splayer = {unib=unib,tnn=tnn,noiseb=noiseb,nsim=nsim}
    val (l,t) = add_time (parmap_queue_extern ncore es splayer) targetl
    val _ =  log rlobj ("Exploration time: " ^ rts t)
    val resultl = combine (targetl, map fst l)
    val nwin = length (filter fst l)
    val _ = log rlobj ("Exploration wins: " ^ its nwin)
    val rlex = List.concat (map snd l)
    val _ = log rlobj ("Exploration new examples: " ^ its (length rlex))
  in
    (rlex,resultl)
  end

fun rl_compete_targetl unib (rlobj,es) tnn targetl =
  rl_explore_targetl (unib,false) (rlobj,es) tnn targetl

(*
fun row_win l =
  case l of [] => 0 | a :: m => if a then 1 + row_win m else 0
fun row_lose l =
  case l of [] => 0 | a :: m => if not a then 1 + row_lose m else 0
fun row_either l = Int.max (row_lose l, row_win l)
fun exists_win l = exists I l

fun stats_select_one rlobj (s,targetl) =
  let
    val il = map (row_either o snd o snd) targetl
    fun f (a,b) = its a ^ "-" ^ its b
    val l = dlist (count_dict (dempty Int.compare) il)
  in
    log rlobj ("  " ^ s ^ " tot-" ^ its (length il) ^ "  " ^
      (String.concatWith " " (map f l)))
  end

fun stats_select rlobj nfin nwin (neg,pos,negsel,possel) =
  let
    val l = [("neg:",neg),("ns :",negsel),("pos:",pos),("ps :",possel)]
  in
    log rlobj ("Exploration: " ^ its nfin ^ " targets ");
    log rlobj ("Exploration: " ^ its nwin ^ " targets proven at least once");
    app (stats_select_one rlobj) l
  end
*)

(*
fun select_from_targetd rlobj ntot targetd =
  let
    val targetwinl = map (fn (a,(b,c,_)) => (a,(b,c))) (dlist targetd)
    fun f x = 1.0 / (1.0 + Real.fromInt x)
    fun g x =
      let
        val y = random_real ()
        val y' = if y < epsilon then epsilon else y
      in
        x / y'
      end
    fun h (a,(b,winl)) = ((a,(b,winl)), (g o f o row_either) winl)
    fun test (_,(_,winl)) = null winl orelse not (hd winl)
    val (neg,pos) = partition test targetwinl
    val negsel = first_n (ntot div 2) (dict_sort compare_rmax (map h neg))
    val possel = first_n (ntot div 2) (dict_sort compare_rmax (map h pos))
    val lfin = map (fst o fst) (rev negsel @ possel)
    val lwin = filter exists_win (map (snd o snd) targetwinl)
    
  in
    stats_select rlobj (length lfin)
       (length lwin) (neg,pos, map fst negsel, map fst possel);
    lfin
  end
*)

fun select_from_targetd rlobj ntot targetd = dkeys targetd
  (* map (#modify_board rlobj targetd) *)

fun update_targetd ((board,b),targetd) =
  let val bl = dfind board targetd handle NotFound => [] in
    dadd board (b :: bl) targetd
  end

fun rl_explore_targetd unib (rlobj,es) (tnn,targetd) =
  let
    val rlparam = #rlparam rlobj
    val targetl = select_from_targetd rlobj (#ntarget rlparam) targetd
    val (rlex,resultl) =
      rl_explore_targetl (unib,true) (rlobj,es) tnn targetl
    val newtargetd = foldl update_targetd targetd resultl
  in
    (rlex,newtargetd)
  end

fun rl_explore_init ngen (rlobj,es) targetd =
  let
    val _ = log rlobj "Exploration: initialization"
    val dummy = random_tnn (#tnnparam (#dplayer rlobj))
    val rlparam = #rlparam rlobj
    val targetl = select_from_targetd rlobj (#ntarget rlparam) targetd
    val (rlex,resultl) =
      rl_explore_targetl (true,false) (rlobj,es) dummy targetl
    val newtargetd = foldl update_targetd targetd resultl
  in
    store_rlex rlobj ngen rlex;
    store_targetd rlobj ngen newtargetd;
    (rlex,newtargetd)
  end

fun rl_explore_cont ngen (rlobj,es) (tnn,rlex,targetd) =
  let
    val (rlex1,newtargetd) = rl_explore_targetd false (rlobj,es) (tnn,targetd)
    val rlex2 = first_n (#exwindow (#rlparam rlobj)) (rlex1 @ rlex)
  in
    store_rlex rlobj ngen rlex1;
    store_targetd rlobj ngen newtargetd;
    (rlex2, newtargetd)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_loop ngen (rlobj,es) (rlex,targetd) =
  let
    val _ = log rlobj ("\nGeneration " ^ its ngen)
    val tnn = rl_train ngen rlobj rlex
    val (newrlex,newtargetd) = rl_explore_cont ngen (rlobj,es) (tnn,rlex,targetd)
  in
    rl_loop (ngen + 1) (rlobj,es) (newrlex,newtargetd)
  end

fun rl_start (rlobj,es) targetd =
  let
    val expdir = eval_dir ^ "/" ^ #expname (#rlparam rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
    val (rlex,newtargetd) = rl_explore_init 0 (rlobj,es) targetd
  in
    rl_loop 1 (rlobj,es) (rlex,newtargetd)
  end

fun rl_restart ngen (rlobj,es) targetd =
  let
    val expdir = eval_dir ^ "/" ^ #expname (#rlparam rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
    val rlex = retrieve_rlex rlobj ngen
  in
    rl_loop (ngen + 1) (rlobj,es) (rlex,targetd)
  end

(* -------------------------------------------------------------------------
   Final MCTS Testing
   ------------------------------------------------------------------------- *)

(*
type 'a ftes = (unit, 'a, bool * int * 'a option) smlParallel.extspec
type 'a fttnnes = (tnn, 'a, bool * int * 'a option) smlParallel.extspec

fun option_to_list vo = if isSome vo then [valOf vo] else []
fun list_to_option l =
  case l of [] => NONE | [a] => SOME a | _ => raise ERR "list_to_option" ""

fun ft_write_result gameio file (b,nstep,boardo) =
  (
  writel (file ^ "_bstatus") [bts b];
  writel (file ^ "_nstep") [its nstep];
  (#write_boardl gameio) (file ^ "_boardo") (option_to_list boardo)
  )

fun ft_read_result gameio file =
  let
    val s1 = singleton_of_list (readl (file ^ "_bstatus"))
    val s2 = singleton_of_list (readl (file ^ "_nstep"))
  in
    (
    string_to_bool s1,
    string_to_int s2,
    list_to_option ((#read_boardl gameio) (file ^ "_boardo"))
    )
  end

val ft_mctsparam =
  {
  timer = SOME 60.0,
  nsim = NONE, stopatwin_flag = true,
  decay = 1.0, explo_coeff = 2.0,
  noise_all = false, noise_root = false,
  noise_coeff = 0.25, noise_gen = random_real,
  noconfl = false, avoidlose = false
  }

fun mk_ft_mctsparam tim =
  {
  timer = SOME tim,
  nsim = NONE, stopatwin_flag = true,
  decay = 1.0, explo_coeff = 2.0,
  noise_all = false, noise_root = false,
  noise_coeff = 0.25, noise_gen = random_real,
  noconfl = false, avoidlose = false
  }

fun ft_extsearch_fun rlobj player (_:unit) target =
  let
    val mctsobj =
      {mctsparam = ft_mctsparam, game = #game rlobj, player = player}
    val (tree,_) = mcts mctsobj (starttree_of mctsobj target)
    val b = is_win (#status (dfind [] tree))
    val boardo = if not b then NONE else
      let val nodel = trace_win tree [] in
        SOME (#board (last nodel))
      end
  in
    (b,dlength tree-1,boardo)
  end

fun ft_mk_extsearch self (rlobj as {rlparam,gameio,...}) player =
  {
  self = self,
  parallel_dir = default_parallel_dir ^ "_finaltest",
  reflect_globals = fn () => "()",
  function = ft_extsearch_fun rlobj player,
  write_param = fn _ => (fn _ => ()),
  read_param = fn _ => (),
  write_arg = write_target gameio,
  read_arg = read_target gameio,
  write_result = ft_write_result gameio,
  read_result = ft_read_result gameio
  }


fun fttnn_extsearch_fun rlobj tnn target =
  let
    val pretob = #pretob (#dplayer rlobj)
    val game = #game rlobj
    fun preplayer target' =
      let val tob = pretob (SOME (target',tnn)) in
        fn board => player_from_tnn tnn tob game board
      end
    val mctsobj =
      {mctsparam = ft_mctsparam, game = #game rlobj,
       player = preplayer target}
    val (tree,_) = mcts mctsobj (starttree_of mctsobj target)
    val b = #status (dfind [] tree) = Win
    val boardo = if not b then NONE else
      let val nodel = trace_win tree [] in
        SOME (#board (last nodel))
      end
  in
    (b,dlength tree-1,boardo)
  end

fun fttnn_mk_extsearch self (rlobj as {rlparam,gameio,...}) =
  {
  self = self,
  parallel_dir = default_parallel_dir ^ "_finaltest",
  reflect_globals = fn () => "()",
  function = fttnn_extsearch_fun rlobj,
  write_param = (fn file => (fn tnn => write_tnn (file ^ "_tnn") tnn)),
  read_param = (fn file => read_tnn (file ^ "_tnn")),
  write_arg = write_target gameio,
  read_arg = read_target gameio,
  write_result = ft_write_result gameio,
  read_result = ft_read_result gameio
  }


fun mk_dis tree =
  let
    val pol = #pol (dfind [] tree)
    val _ = if null pol then raise ERR "mk_dis" "pol" else ()
    fun f (_,cid) = #vis (dfind cid tree) handle NotFound => 0.0
    val dis = map_assoc f pol
    val tot = sum_real (map snd dis)
    val _ = if tot < 0.5 then raise ERR "mk_dis" "tot" else ()
  in
    (dis,tot)
  end

fun select_bigstep tree = snd (best_in_distrib (fst (mk_dis tree)))

fun fttnnbs_extsearch_fun rlobj tnn target =
  let
    val pretob = #pretob (#dplayer rlobj)
    val game = #game rlobj
    fun preplayer target' =
      let val tob = pretob (SOME (target',tnn)) in
        fn board => player_from_tnn tnn tob game board
      end
    val timerl = List.tabulate (30, fn _ => int_div 60 30)
    val startmctsobj =
      {mctsparam = mk_ft_mctsparam (hd timerl), game = #game rlobj,
       player = preplayer target}
    val (starttree,startcache) = starttree_of startmctsobj target
    fun loop timl (tree,cache) =
      if null timl then (false, 8, NONE) else
      let
        val mctsobj =
          {mctsparam = mk_ft_mctsparam (hd timl), game = #game rlobj,
           player = preplayer target}
        val (endtree,_) = mcts mctsobj (tree,cache)
        val cid = select_bigstep endtree
        val status = #status (dfind [] endtree)
      in
        if status = Undecided
          then
            let
              val newtree = cut_tree cid endtree
              val newcache = build_cache game newtree
            in
              loop (tl timl) (newtree,newcache)
            end
        else if status = Win
          then
            let val nodel = trace_win endtree [] in
              (status = Win, 8 - length timl, SOME (#board (last nodel)))
            end
        else (status = Win, 8 - length timl, NONE)
      end
  in
    loop timerl (starttree,startcache)
  end

fun fttnnbs_mk_extsearch self (rlobj as {rlparam,gameio,...}) =
  {
  self = self,
  parallel_dir = default_parallel_dir ^ "_finaltest",
  reflect_globals = fn () => "()",
  function = fttnnbs_extsearch_fun rlobj,
  write_param = (fn file => (fn tnn => write_tnn (file ^ "_tnn") tnn)),
  read_param = (fn file => read_tnn (file ^ "_tnn")),
  write_arg = write_target gameio,
  read_arg = read_target gameio,
  write_result = ft_write_result gameio,
  read_result = ft_read_result gameio
  }
*)


end (* struct *)
