(* ========================================================================= *)
(* FILE          : mlReinforce.sml                                           *)
(* DESCRIPTION   : Environnement for reinforcement learning                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mlReinforce :> mlReinforce =
struct

open HolKernel Abbrev boolLib aiLib psMCTS psBigSteps 
mlTreeNeuralNetwork smlParallel

val ERR = mk_HOL_ERR "mlReinforce"

(* -------------------------------------------------------------------------
   All parameters of the reinforcement learning loop
   ------------------------------------------------------------------------- *)

type 'a level_param =
  {
  ntarget_compete : int, ntarget_explore : int,
  level_start : int, level_threshold : real,
  level_targetl : int -> int -> 'a list
  }
type rl_param =
  {
  expname : string, 
  ex_window : int, ex_uniq : bool, 
  ngen : int,
  ncore_search : int, ncore_train : int
  }
type 'a pre_extsearch = 
  {
  write_targetl : string -> 'a list -> unit,
  read_targetl : string -> 'a list,  
  write_exl : string -> 'a ex list -> unit,
  read_exl : string -> 'a ex list,
  write_player : string -> (bool * dhtnn * bool) -> unit,
  read_player : string -> (bool * dhtnn * bool)
  }
type 'a extsearch =
  (bool * mlTreeNeuralNetwork.dhtnn * bool, 'a, bool * 'a ex list) 
  smlParallel.extspec
type ('a,'b) rl_preobj =
  {
  rl_param : rl_param,
  level_param : 'a level_param,
  max_bigsteps : 'a -> int,
  game : ('a,'b) game,
  pre_extsearch : 'a pre_extsearch, 
  dhtnn_param : dhtnn_param,
  term_of_board : 'a -> term
  }
type 'a rl_obj =
  {
  rl_param : rl_param,
  level_param : 'a level_param,
  extsearch : 'a extsearch, 
  dhtnn_param : dhtnn_param,
  term_of_board : 'a -> term
  }

(* -------------------------------------------------------------------------
   Search parallelization (big steps)
   ------------------------------------------------------------------------- *)

fun mk_mcts_param noiseb rl_preobj =
  {
  nsim = 1600,
  stopatwin_flag = false,
  decay = 0.99,
  explo_coeff = 2.0,
  noise_flag = noiseb,
  noise_coeff = 0.25,
  noise_alpha = 0.2
  }
  
fun player_from_dhtnn game (term_of_board,dhtnn) board =
   let val (e,p) = infer_dhtnn dhtnn (term_of_board board) in
     (e, combine (#movel game,p))
   end

fun mk_bigsteps_obj rl_preobj (unib,dhtnn,noiseb) =
  let 
    val game = #game rl_preobj
    val player = 
      if unib 
      then uniform_player game
      else player_from_dhtnn game (#term_of_board rl_preobj,dhtnn) 
  in
    {
    verbose = false, 
    temp_flag = false,
    max_bigsteps = #max_bigsteps rl_preobj,
    mcts_obj = 
       {mcts_param = mk_mcts_param noiseb rl_preobj,
        game = #game rl_preobj,
        player = player}
    }
  end

fun extsearch_fun rl_preobj (unib,dhtnn,noiseb) target =
  let 
    val obj = mk_bigsteps_obj rl_preobj (unib,dhtnn,noiseb)
    val (bstatus,exl,_) = run_bigsteps obj target
  in
    (bstatus,exl)
  end

fun mk_extsearch self rl_preobj =
  let 
    val rl_param = #rl_param rl_preobj
    val {write_targetl,read_targetl,
         write_exl,read_exl,
         write_player,read_player} = #pre_extsearch rl_preobj
    fun write_result file (b,exl) =
      (writel (file ^ "_bstatus") [bts b]; 
       write_exl (file ^ "_exl") exl)
    fun read_result file =
      let val r = 
        (string_to_bool (only_hd (readl (file ^ "_bstatus"))),
         read_exl (file ^ "_exl"))
      in
        app remove_file [file ^ "_bstatus",file ^ "_exl"]; r
      end
  in
    {
    self = self,
    parallel_dir = default_parallel_dir ^ "__" ^ #expname rl_param,
    reflect_globals = fn () => "()",
    function = extsearch_fun rl_preobj,
    write_param = write_player,
    read_param = read_player,
    write_argl = write_targetl,
    read_argl = read_targetl,
    write_result = write_result,
    read_result = read_result
    }
  end

fun mk_rl_obj rl_preobj extsearch =
  {
  rl_param = #rl_param rl_preobj,
  level_param = #level_param rl_preobj,
  extsearch = extsearch, 
  dhtnn_param = #dhtnn_param rl_preobj,
  term_of_board = #term_of_board rl_preobj
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

fun log_header (obj : 'a rl_obj) =
  let
    val param = #rl_param obj
    val name = "expname: " ^ (#expname param)
    val gen1 = "ngen: " ^ its (#ngen param)
    val ex0 = "ex_uniq: " ^ bts (#ex_uniq param)
    val ex1 = "ex_window: " ^ its (#ex_window param)
  in
    log obj "Global parameters";
    log obj (String.concatWith "\n  " ([name,gen1,ex0,ex1]) ^ "\n")
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun stats_exl rl_obj epex =
  let
    val d = count_dict (dempty Term.compare) (map #1 epex)
    val r = average_real (map (Real.fromInt o snd) (dlist d))
  in
    log rl_obj ("Examples: " ^ its (length epex));
    log rl_obj ("Average duplicates: " ^ rts r)
  end

fun rl_train rl_obj exl =
  let
    val exl' = map (fn (a,b,c) => (#term_of_board rl_obj a, b, c)) exl
    val _ = stats_exl rl_obj exl'
    val dhtnn = random_dhtnn (#dhtnn_param rl_obj)
    val schedule = 
      [{ncore = #ncore_train (#rl_param rl_obj),
        verbose = true,
        learning_rate = 0.02,
        batch_size = 16,
        nepoch = 100}]
    val (newdhtnn,t) = add_time (train_dhtnn schedule dhtnn) exl'
  in
    log rl_obj ("Training time : " ^ rts t); 
    newdhtnn
  end


(* -------------------------------------------------------------------------
   Competition
   ------------------------------------------------------------------------- *)

fun compete_one rl_obj dhtnn targetl =
  let
    val ncore = #ncore_search (#rl_param rl_obj)
    val extspec = #extsearch rl_obj
    val player = (false,dhtnn,false)
    val (r,t) = add_time (parmap_queue_extern ncore extspec player) targetl
    val nwin = length (filter fst r)
  in
    log rl_obj ("Competition time : " ^ rts t); 
    log rl_obj ("Competition wins : " ^ its nwin); 
    nwin
  end

fun log_compete rl_obj b newlevel (w_old,w_new) freq =
  let val s = if w_new >= w_old then "Passed" else "Failed" in
    log rl_obj s;
    log rl_obj ("Max success rate: " ^ rts (approx 4 freq));
    if b then log rl_obj ("Level up: " ^ its newlevel) else ()
  end

fun rl_compete rl_obj level dhtnn_old dhtnn_new =
  let
    val {ntarget_compete, ntarget_explore,
         level_start, level_threshold,
         level_targetl} = #level_param rl_obj
    val targetl = level_targetl level ntarget_compete
    val _ = log rl_obj ("Competition targets: " ^ its (length targetl))
    val w_old = compete_one rl_obj dhtnn_old targetl
    val w_new = compete_one rl_obj dhtnn_new targetl
    val freq = int_div (Int.max (w_new,w_old)) (length targetl)
    val b = freq > level_threshold
    val newlevel = if b then level + 1 else level
  in
    log_compete rl_obj b newlevel (w_old,w_new) freq;
    if w_new >= w_old then (newlevel, dhtnn_new) else (newlevel, dhtnn_old)
  end

(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

(*
fun mk_uniq_ex exl =
  let fun cmp ((a,_,_),(b,_,_)) = Term.compare (a,b) in
    mk_sameorder_set cmp exl
  end
*)

fun explore_one rl_obj unib dhtnn targetl =
  let 
    val ncore = #ncore_search (#rl_param rl_obj)
    val extspec = #extsearch rl_obj
    val player = (unib,dhtnn,true)
    val (l,t) = add_time (parmap_queue_extern ncore extspec player) targetl
    val nwin = length (filter fst l)
    val exl = map snd l
  in
    log rl_obj ("Exploration time: " ^ rts t);
    log rl_obj ("Exploration wins: " ^ its nwin);
    log rl_obj ("Exploration new examples: " ^ its (length exl));
    (nwin,exl)
  end

fun rl_explore rl_obj level unib dhtnn allex =
  let
    val rl_param = #rl_param rl_obj
    val {ntarget_compete, ntarget_explore,
         level_start, level_threshold,
         level_targetl} = #level_param rl_obj
    val targetl = level_targetl level ntarget_explore
    val _ = log rl_obj ("Exploration targets: " ^ its (length targetl))
    val (nwin,exl0) = explore_one rl_obj unib dhtnn targetl
    val exl1 = List.concat exl0 @ allex
    (* val exl2 = if #ex_uniq rl_param then mk_uniq_ex exl1 else exl1 *)
    val exl3 = first_n (#ex_window rl_param) exl1
    val b = int_div nwin (length targetl) > level_threshold
    val newlevel = if b then level + 1 else level
  in
    if b then log rl_obj ("Level up: " ^ its newlevel) else ();
    (b,exl3,newlevel)
  end

fun loop_rl_explore rl_obj level unib dhtnn exl =
  let val (b,newexl,newlevel) = rl_explore rl_obj level unib dhtnn exl in
    if b 
    then loop_rl_explore rl_obj newlevel unib dhtnn newexl 
    else (newexl,newlevel)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_init (rl_obj :'a rl_obj) =
  let
    val expname = #expname (#rl_param rl_obj)
    val level = #level_start (#level_param rl_obj)
    val _ = remove_file (eval_dir ^ "/" ^ expname)
    val _ = log_header rl_obj
    val _ = log rl_obj "Generation 0"
    val file = eval_dir ^ "/" ^ expname ^ "_gen0"
    val dhtnn = random_dhtnn (#dhtnn_param rl_obj)
    val _ = write_dhtnn (file ^ "_dhtnn") dhtnn
    val (allex,newlevel) = loop_rl_explore rl_obj level true dhtnn []
  in
    (* write_dhex (file ^ "_allex") allex; *)
    (allex,dhtnn,newlevel)
  end

fun rl_one n rl_obj (allex,dhtnn,level) =
  let
    val expname = #expname (#rl_param rl_obj)
    val file = eval_dir ^ "/" ^ expname ^ "_gen" ^ its n
    val _ = log rl_obj ("\nGeneration " ^ its n)
    val dhtnn_new = rl_train rl_obj allex
    val (level1,dhtnn_best) = rl_compete rl_obj level dhtnn dhtnn_new
    val _ = write_dhtnn (file ^ "_dhtnn") dhtnn_best
    val (newallex,level2) = loop_rl_explore rl_obj level1 false dhtnn allex
  in
    (* write_dhex (file ^ "_allex") newallex; *)
    (newallex,dhtnn_best,level2)
  end

fun cont_rl_loop rl_obj i rldata =
  if i > #ngen (#rl_param rl_obj) then rldata else
  let val rldata_new = rl_one i rl_obj rldata in
    cont_rl_loop rl_obj (i+1) rldata_new
  end

fun start_rl_loop rl_obj = cont_rl_loop rl_obj 1 (rl_init rl_obj)

end (* struct *)
