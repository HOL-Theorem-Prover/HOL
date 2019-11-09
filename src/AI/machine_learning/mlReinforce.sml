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

type 'a train_descr =
  {
  term_of_board : 'a -> term, 
  schedule : schedule, 
  dhtnn_param : dhtnn_param
  }

type 'a guider_descr =
  { 
  guidername : string,
  dhtnn : dhtnn,
  train_descr : 'a train_descr 
  }

type 'a rl_param =
  {
  expname : string, 
  parallel_dir : string,
  ntarget_compete : int, ntarget_explore : int,
  ex_window : int, ex_uniq : bool,
  ngen : int,
  level_start : int, level_threshold : real,
  level_targetl : int -> int -> 'a list,
  ncore_search : int, 
  par_search : (dhtnn, 'a, bool * 'a ex list) smlParallel.extspec,
  ncore_train : int
  }

(* -------------------------------------------------------------------------
   I/O
   ------------------------------------------------------------------------- *)

fun bts b = if b then "true" else "false"
fun bstatus_to_string b = if b then "win" else "lose"
fun string_to_bstatus s = assoc s [("win",true),("lose",false)]
  handle HOL_ERR _ => raise ERR "string_to_bstatus" ""
fun string_to_bool s =
   if s = "true" then true
   else if s = "false" then false
   else raise ERR "string_to_bool" ""

(* -------------------------------------------------------------------------
   Logs
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/experiments/eval"

fun log_in_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end

fun log rl_param s = (log_in_eval (#expname rl_param) s; print_endline s)

fun log_header (param : 'a rl_param) =
  let
    val file = "expname: " ^ (#expname param)
    val para = "parallel_dir: " ^ (#parallel_dir param)
    val gen1 = "ngen: " ^ its (#ngen param)
    val gen2 = "target_compete: " ^ its (#ntarget_compete param)
    val gen3 = "target_explore: " ^ its (#ntarget_explore param)
    val gen4 = "level_start: " ^ its (#level_start param)
    val gen5 = "level_threshold: " ^ rts (#level_threshold param)
    val ex0 = "ex_uniq: " ^ bts (#ex_uniq param)
    val ex1 = "ex_window: " ^ its (#ex_window param)
  in
    log param "Global parameters";
    log param (String.concatWith "\n  "
      ([file,para] @ [gen1,gen2,gen3,gen4,gen5] @ [ex0,ex1]) ^ "\n")
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun stats_exl param epex =
  let
    val d = count_dict (dempty Term.compare) (map #1 epex)
    val r = average_real (map (Real.fromInt o snd) (dlist d))
  in
    log param ("Examples: " ^ its (length epex));
    log param ("Average duplicates: " ^ rts r)
  end

fun rl_train rl_param train_descr exl =
  let
    val exl' = map (fn (a,b,c) => (#term_of_board train_descr a, b, c)) exl
    val _ = stats_exl rl_param exl'
    val dhtnn = random_dhtnn (#dhtnn_param train_descr)
    val schedule = #schedule train_descr
    val (newdhtnn,t) = add_time (train_dhtnn schedule dhtnn) exl'
  in
    log rl_param ("Training time : " ^ rts t); 
    newdhtnn
  end

(* -------------------------------------------------------------------------
   Competition
   ------------------------------------------------------------------------- *)

fun compete_one rl_param dhtnn targetl =
  let
    val ncore = #ncore_search rl_param
    val extspec = #par_search rl_param
    val (r,t) = add_time (parmap_queue_extern ncore extspec dhtnn) targetl
    val nwin = length (filter fst r)
  in
    log rl_param ("Competition time : " ^ rts t); 
    log rl_param ("Competition wins : " ^ its nwin); 
    nwin
  end

fun log_compete b rl_param (w_old,w_new) freq =
  let val s = if w_new >= w_old then "Passed" else "Failed" in
    log rl_param s;
    log rl_param ("Max success rate: " ^ rts (approx 4 freq));
    if b then log rl_param ("Level up: " ^ its (level + 1)) else ()
  end

fun rl_compete (rl_param:'a rl_param) level (dhtnn_old:dhtnn) (dhtnn_new:dhtnn) =
  let
    val targetl = (#level_targetl rl_param) 
      (!(#level_current rl_param)) (#ntarget_compete rl_param)
    val _ = log rl_param ("Competition targets: " ^ its (length targetl))
    val w_old = compete_one rl_param dhtnn_old targetl
    val w_new = compete_one rl_param dhtnn_new targetl
    val freq = int_div (Int.max (w_new,w_old)) (length targetl)
    val b = freq > #level_threshold rl_param
    val newlevel = if b then level + 1 else level
  in
    log_compete b rl_param (w_old,w_new) freq;
    if w_new >= w_old then (newlevel, dhtnn_new) else (newlevel, dhtnn_old)
  end

(* -------------------------------------------------------------------------
   Exploration
   ------------------------------------------------------------------------- *)

fun mk_uniq_ex exl =
  let fun cmp ((a,_,_),(b,_,_)) = Term.compare (a,b) in
    mk_sameorder_set cmp exl
  end

fun explore_one rl_param dhtnn targetl
  let 
    val ncore = #ncore_search rl_param
    val (l,t) = add_time (parmap_queue_extern ncore extspec param) targetl
    val nwin = length (filter fst l)
    val exl = List.concat (map snd l)
  in
    log rl_param ("Exploration time: " ^ rts t);
    log rl_param ("Exploration wins: " ^ its nwin);
    log rl_param ("Exploration new examples: " ^ its (length exl));
    (nwin,exl)
  end

fun explore rl_param (unib,tnn) allex =
  let
    val targetl = (#level_targetl rl_param) 
      (!(#level_current rl_param)) (#ntarget_explore rl_param)
    val _ = log rl_param ("Exploration targets: " ^ its (length targetl))
    val (nwin,exl0) = explore_one rl_param dhtnn targetl
    val exl1 = List.concat exl0 @ allex
    val exl2 = if #ex_uniq rl_param then mk_uniq_ex exl1 else exl1
    val exl3 = first_n (#ex_window rl_param) exl2
    val b = int_div nwin (length targetl) > #level_threshold rl_param
  in
    (b,exl3)
  end

fun loop_rl_explore rl_param (unib,tnn) exl =
  let val (b,newexl) = explore rl_param (unib,tnn) exl in
    if b then loop_explore rl_param (unib,tnn) newexl else newexl
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_init rl_param =
  let
    val _ = remove_file (eval_dir ^ "/" ^ (#expname rl_param))
    val _ = log_param rl_param
    val _ = log rl_param "Generation 0"
    val file = eval_dir ^ "/" ^ (#expname rl_param) ^ "_gen" ^ its 0
    val tnn_random = random_tnn_gamespec gamespec
    val (_,allex) = loop_rl_explore rl_param (true,tnn_random) []
  in
    write_tnn (file ^ "_tnn") tnn;
    write_dhex (file ^ "_allex") allex;
    (allex, tnn)
  end

fun rl_one n rl_param (allex,tnn) =
  let
    val prefile = eval_dir ^ "/" ^ (#expname rl_param) ^ "_gen" ^ its n
    val _ = log ("\nGeneration " ^ its n)
    val tnn_new = train_f gamespec allex
    val tnn_best = rl_compete (gamespec,extspec) tnn tnn_new
    val _ = write_tnn (prefile ^ "_tnn") tnn_best

    val newallex = loop_explore allex
  in
    write_dhex (prefile ^ "_allex") newallex;
    (newallex,tnn_best)
  end

fun rl_loop rl_param i rldata =
  if i >= #ngen rl_param then rldata else
  let val rldata_new = rl_one i (gamespec,extspec) rldata in
    rl_loop (i+1, nmax) (gamespec,extspec) rldata_new
  end

fun start_rl_loop rl_param =
  let val (allex,tnn) = rl_start rl_param in
    rl_loop rl_param 1 (allex,tnn)
  end

end (* struct *)
