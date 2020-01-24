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

type 'a targetd = ('a, int * bool list) Redblackmap.dict
type 'a gameio =
  {write_boardl : string -> 'a list -> unit,
   read_boardl : string -> 'a list}
type splayer = bool * tnn * bool * int
type 'a dplayer = 
  {tob : 'a -> term list, schedule : schedule, tnnparam : tnnparam}
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

fun mk_mctsparam noiseb nsim rlobj =
  {
  nsim = nsim, stopatwin_flag = false,
  decay = #decay (#rlparam rlobj), explo_coeff = 2.0,
  noise_all = noiseb, noise_root = false,
  noise_coeff = 0.25, noise_gen = random_real,
  noconfl = false, avoidlose = false
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
  handle Subscript => raise ERR "write_splayer" ""

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
  handle Subscript => raise ERR "write_target" ""

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

fun targetd_file rlobj n = 
  eval_dir ^ "/" ^ (#expname (#rlparam rlobj)) ^ "/targetd" ^ its n
fun blts (a,bl) = its a ^ " " ^ String.concatWith " " (map bts bl)
fun stbl s = 
  let val l = (String.tokens Char.isSpace s) in
    (string_to_int (hd l), map string_to_bool (tl l))
  end
fun store_targetd rlobj n targetd =
  let val (l1,l2) = split (dlist targetd) in
    #write_boardl (#gameio rlobj) 
       ((targetd_file rlobj n) ^ "_boardl") l1;
    writel ((targetd_file rlobj n) ^ "_ibl") (map blts l2)
  end
fun retrieve_targetd rlobj n =
  let 
    val l1 = #read_boardl (#gameio rlobj) ((targetd_file rlobj n) ^ "_boardl")
    val l2 = map stbl (readl ((targetd_file rlobj n) ^ "_ibl"))
  in 
    dnew (#board_compare (#game rlobj)) (combine (l1,l2))
  end

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
    val {tob,schedule,tnnparam} = #dplayer rlobj
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
    val splayer = (unib,tnn,noiseb,nsim)
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

fun select_from_targetd rlobj ntot targetd =
  let  
    fun is_new l = length l < 4
    fun is_win k l = not (is_new l) andalso
      (length (filter I (first_n 4 l)) = k)
    fun f k = map fst (filter (fn (_,(_,l)) => is_win k l) (dlist targetd))
    val lnewtot1 = filter (fn (_,(_,l)) => is_new l) (dlist targetd)
    fun cmp ((_,(i1,_)),(_,(i2,_))) = Int.compare (i1,i2)
    val lnewtot2 = map fst (dict_sort cmp lnewtot1)
    val l4tot = f 4
    val l4 = random_subset (ntot div 2) l4tot
    val n4 = ntot - length l4
    val l3tot = f 3
    val l3 = random_subset (n4 div 2) l3tot
    val n3 = n4 - length l3
    val l2tot = f 2
    val l2 = random_subset (n3 div 2) l2tot
    val n2 = n3 - length l2
    val l1tot = f 1
    val l1 = random_subset (n2 div 2) l1tot
    val n1 = n2 - length l1
    val l0tot = f 0
    val l0 = random_subset (if null lnewtot2 then n1 else (n1 div 2)) l0tot
    val n0 = n1 - length l0
    val lnew = first_n n0 lnewtot2
    val lfin = rev (List.concat [l4,l3,l2,l1,l0,lnew])
  in
    log rlobj ("Exploration: " ^ its (length lfin) ^ " targets ");
    log rlobj ("  selection: " ^
      (String.concatWith " " 
      (map (its o length) [l4,l3,l2,l1,l0,lnew])));
    log rlobj ("  distribution: " ^
      (String.concatWith " " 
      (map (its o length) [l4tot,l3tot,l2tot,l1tot,l0tot,lnewtot2])));
    lfin
  end

fun update_targetd ((board,winb),targetd) = 
  let 
    val (i,oldl) = dfind board targetd 
      handle NotFound => raise ERR "update_targetd" ""
  in
    dadd board (i,winb :: oldl) targetd
  end
 
fun rl_explore_targetd unib (rlobj,es) (tnn,targetd) =
  let
    val rlparam = #rlparam rlobj
    val targetl = select_from_targetd rlobj (#ntarget rlparam) targetd
    val (rlex,resultl) = 
      rl_explore_targetl (unib,true) (rlobj,es) tnn targetl
    val newtargetd = foldl update_targetd targetd resultl
  in
    (rlex, newtargetd)
  end

fun rl_explore_init ngen (rlobj,es) targetd = 
  let
    val _ = log rlobj "Exploration: initialization"  
    val dummy = random_tnn (#tnnparam (#dplayer rlobj))
    val (rlex,_) = rl_explore_targetd true (rlobj,es) (dummy,targetd)
  in
    store_rlex rlobj ngen rlex; rlex
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
    val rlex = rl_explore_init 0 (rlobj,es) targetd
  in
    rl_loop 1 (rlobj,es) (rlex,targetd)
  end

fun rl_restart ngen (rlobj,es) targetd =
  let 
    val expdir = eval_dir ^ "/" ^ #expname (#rlparam rlobj)
    val _ = app mkDir_err [eval_dir,expdir]
    val rlex = retrieve_rlex rlobj ngen
  in
    rl_loop (ngen + 1) (rlobj,es) (rlex,targetd)
  end

end (* struct *)
