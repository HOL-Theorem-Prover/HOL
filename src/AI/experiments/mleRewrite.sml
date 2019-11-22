(* ========================================================================= *)
(* FILE          : mleRewrite.sml                                            *)
(* DESCRIPTION   : Term rewriting as a reinforcement learning game           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)


structure mleRewrite :> mleRewrite =
struct

open HolKernel boolLib Abbrev aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mleLib mleArithData

val ERR = mk_HOL_ERR "mleRewrite"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type pos = int list
type board = ((term * pos) * int)

fun mk_startboard tm = ((tm,[]), 2 * lo_prooflength 200 tm + 2)
fun dest_startboard ((tm,_),_) = tm

(* search and networks have to be aware of the length of the proof *)
fun status_of ((tm,_),n) =
  if is_suc_only tm then Win
  else if n <= 0 then Lose
  else Undecided

fun max_bigsteps target = snd target + 1

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val numtag = mk_var ("numtag", ``:num -> num``)

fun tag_pos (tm,pos) =
  if null pos then (if is_eq tm then tm else mk_comb (numtag,tm)) else
  let
    val (oper,argl) = strip_comb tm
    fun f i arg = if i = hd pos then tag_pos (arg,tl pos) else arg
  in
    list_mk_comb (oper, mapi f argl)
  end

val rewrite_operl =
  let val operl' = (numtag,1) :: operl_of (``0 * SUC 0 + 0 = 0``) in
    mk_fast_set oper_compare operl'
  end

fun term_of_board ((tm,pos),_) = tag_pos (tm,pos)

val board_compare =
  cpl_compare
    (cpl_compare Term.compare (list_compare Int.compare))
    Int.compare

fun string_of_board b = term_to_string (term_of_board b)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Arg of int | Paramod of (int * bool)

val movel =
  map Arg [0,1] @
  [Paramod (0,true),Paramod (0,false)] @
  [Paramod (1,true),Paramod (1,false)] @
  [Paramod (2,true)] @
  [Paramod (3,true),Paramod (3,false)]

fun move_compare (m1,m2) = case (m1,m2) of
    (Arg i1, Arg i2) => Int.compare (i1,i2)
  | (Arg _, _) => LESS
  | (_,Arg _) => GREATER
  | (Paramod (i1,b1), Paramod (i2,b2)) =>
    (cpl_compare Int.compare bool_compare) ((i1,b1),(i2,b2))

fun string_of_move move = case move of
    Arg n => ("A" ^ its n)
  | Paramod (i,b) => ("P" ^ its i ^ (if b then "t" else "f"))

fun narg tm = length (snd (strip_comb tm))

fun argn_pb n (tm,pos) = (tm,pos @ [n])

fun paramod_pb (i,b) (tm,pos) =
  let
    val ax = Vector.sub (robinson_eq_vect,i)
    val tmo = paramod_ground (if b then ax else sym ax) (tm,pos)
  in
    (valOf tmo,[])
  end

fun available_move ((tm,pos),_) move = case move of
    Arg i => (narg (find_subtm (tm,pos)) >= i + 1)
  | Paramod (i,b) => can (paramod_pb (i,b)) (tm,pos)

fun apply_move move ((tm,pos),step) = case move of
    Arg n => (argn_pb n (tm,pos), step - 1)
  | Paramod (i,b) => (paramod_pb (i,b) (tm,pos), step - 1)


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
  available_move = available_move,
  apply_move = apply_move
  }

(* -------------------------------------------------------------------------
   Level
   ------------------------------------------------------------------------- *)

fun create_levels () =
  let
    val filein = dataarith_dir ^ "/train"
    val fileout = dataarith_dir ^ "/train_plsorted"
    val l1 = import_terml filein
    val _ = print_endline ("Reading " ^ its (length l1) ^ " terms")
    val l2 = mapfilter (fn x => (x, lo_prooflength 200 x)) l1
    val l3 = filter (fn x => snd x <= 100) l2
    val l4 = dict_sort compare_imin l3
  in
    print_endline ("Exporting " ^ its (length l4) ^ " terms");
    export_terml fileout (map fst l4)
  end

fun level_targetl level ntarget =
  let
    val tml = mlTacticData.import_terml (dataarith_dir ^ "/train_plsorted")
    val tmll = map shuffle (first_n level (mk_batch 400 tml))
    val tml2 = List.concat (list_combine tmll)
  in
    map mk_startboard (first_n ntarget tml2)
  end

fun max_prooflength_atgen () =
  let val tml = import_terml (dataarith_dir ^ "/train_plsorted") in
    map (list_imax o map (lo_prooflength 1000)) (mk_batch 400 tml)
  end

fun stats_prooflength file =
  let
    val l0 = import_terml file
    val l1 = mapfilter (fn x => (x,(lo_prooflength 200) x)) l0
    val _  = print_endline (its (length l1))
    val l2 = dlist (dregroup Int.compare (map swap l1))
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
    writel (file ^ "_pos") (map string_of_pos l1b);
    writel (file ^ "_max") (map its l2)
  end
fun read_boardl file =
  let
    val orgl = import_terml (file ^ "_orgtm")
    val posl = map pos_of_string (readl (file ^ "_pos"))
    val nl = map string_to_int (readl (file ^ "_max"))
  in
    combine (combine (orgl,posl), nl)
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
  operl = rewrite_operl, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 12, dimpoli = length movel
  }

val dplayer =
  {playerid = "only_player", dhtnn_param = dhtnn_param, schedule = schedule}

val pretobdict = dnew String.compare 
  [("only_player", (term_of_board, fn () => term_of_board))];

(* -------------------------------------------------------------------------
   Reinforcement learning
   ------------------------------------------------------------------------- *)

val expname = "mleRewrite-v2-1"

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

val extsearch = mk_extsearch "mleRewrite.extsearch" rlpreobj

val rlobj = mk_rlobj rlpreobj extsearch

(*
load "mlReinforce"; open mlReinforce;
load "mleRewrite"; open mleRewrite;
(* create_levels (); *)
val r = start_rl_loop rlobj;
*)

end (* struct *)
