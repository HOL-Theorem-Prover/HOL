(* ========================================================================= *)
(* FILE          : mleSynthesize.sml                                         *)
(* DESCRIPTION   : Specification of a term synthesis game                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSynthesize :> mleSynthesize =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mleLib mleArithData

val ERR = mk_HOL_ERR "mleSynthesize"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = ((term * int) * term)

fun string_of_board ((a,b),c)= tts a ^ " " ^ its b ^ " " ^ tts c

val board_compare =
  cpl_compare (cpl_compare Term.compare Int.compare) Term.compare

val active_var = ``active_var:num``;

fun mk_startboard tm = ((tm,mleArithData.eval_numtm tm),active_var)
fun dest_startboard ((tm,_),_) = tm

fun is_ground tm = not (tmem active_var (free_vars_lr tm))

val synt_operl = [(active_var,0)] @ operl_of ``SUC 0 + 0 = 0 * 0``
fun term_of_board ((ctm,_),tm) = mk_eq (ctm,tm)

fun status_of ((ctm,n),tm) =
  if is_ground tm andalso mleArithData.eval_numtm tm = n then Win
  else if is_ground tm orelse
    term_size tm > 2 * Int.min (n,term_size ctm) + 1
    then Lose
  else Undecided

(* anything greater than the bound provided by status_of works *)
fun max_bigsteps ((ctm,n),_) = 4 * Int.max (n,term_size ctm) + 5

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term * int)
val movel = operl_of ``SUC 0 + 0 * 0``;
val move_compare = cpl_compare Term.compare Int.compare

fun action_oper (oper,n) tm =
  let
    val res = list_mk_comb (oper, List.tabulate (n, fn _ => active_var))
    val sub = [{redex = active_var, residue = res}]
  in
    subst_occs [[1]] sub tm
  end

fun apply_move move (ctmn,tm) = (ctmn, action_oper move tm)

fun string_of_move (tm,_) = tts tm

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  board_compare = board_compare,
  string_of_board = string_of_board,
  movel = movel,
  move_compare = move_compare,
  string_of_move = string_of_move,
  status_of = status_of,
  available_move = (fn a => (fn b => true)),
  apply_move = apply_move
  }

(* -------------------------------------------------------------------------
   Level
   ------------------------------------------------------------------------- *)

val train_file = dataarith_dir ^ "/train"
fun min_sizeeval x = Int.min (term_size x, eval_numtm x)

fun order_train baseout f =
  let
    val l1 = import_terml train_file
    val _ = print_endline ("Reading " ^ its (length l1) ^ " terms")
    val l2 = map (fn x => (x, f x)) l1
    val l3 = dict_sort compare_imin l2
  in
    print_endline ("Exporting " ^ its (length l3) ^ " terms");
    export_terml (dataarith_dir ^ "/" ^ baseout) (map fst l3)
  end

fun level_targetl level ntarget =
  let
    val tml1 = import_terml (dataarith_dir ^ "/train_sizeeval_sorted")
    val tmll2 = map shuffle (first_n level (mk_batch 400 tml1))
    val tml3 = List.concat (list_combine tmll2)
  in
    map mk_startboard (first_n ntarget tml3)
  end

fun create_levels () = order_train "train_sizeeval_sorted" min_sizeeval

fun max_sizeeval_atgen () =
  let val tml = import_terml (dataarith_dir ^ "/train_sizeeval_sorted") in
    map (list_imax o map min_sizeeval) (mk_batch 400 tml)
  end

fun stats_sizeeval file =
  let
    val l0 = import_terml file
    val l1 = map (fn x => (x,min_sizeeval x)) l0;
    val l1' = filter (fn x => snd x <= 100) l1;
    val _  = print_endline (its (length l1'));
    val l2 = dlist (dregroup Int.compare (map swap l1'));
  in
    map_snd length l2
  end

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_target file target =
  export_terml (file ^ "_target") [dest_startboard target]
fun read_target file =
  mk_startboard (only_hd (import_terml (file ^ "_target")))

fun write_boardl file boardl =
  let
    val (l1,l2) = split boardl
    val (l1a,l1b) = split l1
  in
    export_terml (file ^ "_orgtm") l1a;
    writel (file ^ "_int") (map its l1b);
    export_terml (file ^ "_newtm") l2
  end
fun read_boardl file =
  let
    val l1 = import_terml (file ^ "_orgtm")
    val l2 = map string_to_int (readl (file ^ "_int"))
    val l3 = import_terml (file ^ "_newtm")
  in
    combine (combine (l1,l2),l3)
  end

fun write_exl file exl =
  let val (boardl,evall,polil) = split_triple exl in
    write_boardl (file ^ "_boardl") boardl;
    writel (file ^ "_eval") (map reall_to_string evall);
    writel (file ^ "_poli") (map reall_to_string polil)
  end
fun read_exl file =
  let
    val evall = map string_to_reall (readl (file ^ "_eval"))
    val polil = map string_to_reall (readl (file ^ "_poli"))
    val boardl = read_boardl (file ^ "_boardl")
  in
    combine_triple (boardl,evall,polil)
  end

fun write_splayer file (unib,dhtnn,noiseb,playerid,nsim) =
  (
  write_dhtnn (file ^ "_dhtnn") dhtnn;
  writel (file ^ "_flags") [String.concatWith " " (map bts [unib,noiseb])];
  writel (file ^ "_playerid") [playerid];
  writel (file ^ "_nsim") [its nsim]
  )
fun read_splayer file =
  let
    val dhtnn = read_dhtnn (file ^ "_dhtnn")
    val (unib,noiseb) =
      pair_of_list (map string_to_bool
        (String.tokens Char.isSpace (only_hd (readl (file ^ "_flags")))))
    val playerid = only_hd (readl (file ^ "_playerid"))
    val nsim = string_to_int (only_hd (readl (file ^ "_nsim")))
  in
    (unib,dhtnn,noiseb,playerid,nsim)
  end

val pre_extsearch =
  {
  write_target = write_target,
  read_target = read_target,
  write_exl = write_exl,
  read_exl = read_exl,
  write_splayer = write_splayer,
  read_splayer = read_splayer
  }

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 1, verbose = true,
    learning_rate = 0.02,
    batch_size = 16, nepoch = 100}]

val dhtnn_param =
  {
  operl = synt_operl, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 12, dimpoli = length movel
  }

val dplayer =
  {playerid = "only_player", dhtnn_param = dhtnn_param, schedule = schedule}

val pretobdict =
  dnew String.compare [("only_player",
    (term_of_board, fn () => term_of_board))];

(* -------------------------------------------------------------------------
   Reinforcement learning
   ------------------------------------------------------------------------- *)

val expname = "mleSynthesize-v2-1"

val level_param =
  {
  ntarget_start = 400, ntarget_compete = 400, ntarget_explore = 400,
  level_start = 1, level_threshold = 0.95,
  level_targetl = level_targetl
  }

val rl_param =
  {
  expname = expname, ex_window = 40000, ex_filter = NONE,
  skip_compete = false,
  ngen = 100, ncore_search = 40,
  nsim_start = 1600, nsim_explore = 1600, nsim_compete = 1600,
  decay = 0.99
  }

val rlpreobj : (board,move,unit) rlpreobj =
  {
  rl_param = rl_param,
  level_param = level_param,
  max_bigsteps = max_bigsteps,
  game = game,
  pre_extsearch = pre_extsearch,
  pretobdict = pretobdict,
  precomp_dhtnn = (fn _ => (fn _ => ())),
  dplayerl = [dplayer]
  }

val extsearch = mk_extsearch "mleSynthesize.extsearch" rlpreobj

val rlobj = mk_rlobj rlpreobj extsearch

(*
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
(* create_levels (); *)
val r = start_rl_loop rlobj;
*)


end (* struct *)
