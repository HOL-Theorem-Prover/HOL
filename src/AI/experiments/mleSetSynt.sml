(* ========================================================================= *)
(* FILE          : mleSetSynt.sml                                            *)
(* DESCRIPTION   : Specification of a term synthesis game                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSetSynt :> mleSetSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData mlReinforce mleLib mleSetLib

val ERR = mk_HOL_ERR "mleSetSynt"

(* -------------------------------------------------------------------------
   Global parameter
   ------------------------------------------------------------------------- *)

val graph_size = 64

(* -------------------------------------------------------------------------
   Helpers
   ------------------------------------------------------------------------- *)

val graphcat = mk_var ("graphcat", ``:bool -> bool -> bool``)
val adjgraph = mk_var ("adjgraph", ``: bool -> bool -> bool``);

val uncont_term = mk_var ("uncont_term",alpha)
val uncont_form = mk_var ("uncont_form",bool)
val uncontl = [uncont_term,uncont_form]

fun rw_to_uncont t =
  let val (oper,argl) = strip_comb t in
    if term_eq oper cont_term then uncont_term
    else if term_eq oper cont_form then uncont_form
    else list_mk_comb (oper, map rw_to_uncont argl)
  end

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = ((term * bool list) * term)

fun board_compare (((a,b),c),((d,e),f)) = 
  cpl_compare Term.compare Term.compare ((c,a),(f,d))

fun string_of_board ((_,bl),tm) =
  String.concatWith " " (map bts bl) ^ " :\n" ^ tts tm

fun mk_startboard tm = ((tm,mk_graph graph_size tm),start_form)
fun dest_startboard ((tm,_),_) = tm

fun status_of ((orgtm,graph),tm) =
  if not (can (find_term is_cont) tm) then
    if has_graph graph tm handle HOL_ERR _ => false
    then Win
    else Lose
  else if term_size (rw_to_uncont tm) > 2 * term_size orgtm
    then Lose
    else Undecided

(* -------------------------------------------------------------------------
   1) Term representation of the board (default)
   ------------------------------------------------------------------------- *)

val graphtag = mk_var ("graphtag", ``:bool -> bool``)

fun string_of_graph graph =
  String.concatWith " " (map bts graph)
fun graph_of_string s =
  map string_to_bool (String.tokens Char.isSpace s)

fun numvar_of_graph dim graph =
  if length graph = dim then 
  let
    val vs = tnn_numvar_prefix ^
      String.concat (map (fn x => if x then "1" else "0") graph)
  in
    mk_var (vs,bool)
  end
  else raise ERR "numvar_of_graph" ""

fun term_of_graph dim graph =
  let 
    val graphl = mk_batch_full dim graph
    val lastg1 = last graphl
    val lastg2 = lastg1 @ List.tabulate (dim - length lastg1, fn _ => false)
    val numvarl = map (numvar_of_graph dim) (butlast graphl @ [lastg2])
  in
    list_mk_binop graphcat numvarl
  end

fun term_of_board1 dim ((_,graph),tm) =
  list_mk_comb (adjgraph, [term_of_graph dim graph, rw_to_uncont tm])

val operl1 = mk_fast_set oper_compare
  (map_assoc arity_of (graphcat :: adjgraph :: (uncontl @ operl_plain)))


(*
load "aiLib"; open aiLib;
load "mleSetLib"; open mleSetLib;
load "mleSetSynt"; open mleSetSynt;

val l1 = parse_setsyntdata ();
val tml = map fst l1;
val graph = List.tabulate (64,fn _ => true);
val board : board = ((T,graph), random_elem tml);
val tm1 = term_of_board1 12 board;
*)

(*
load "aiLib"; open aiLib;
load "mleSetLib"; open mleSetLib;
load "mleSetSynt"; open mleSetSynt;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mlNeuralNetwork"; open mlNeuralNetwork;

val graph = List.tabulate (64,fn _ => true);
val tmgraph = term_of_graph 12 graph;
val dhtnn = random_dhtnn dhtnn_param_base;
val embed1 = time (infer_dhtnn_nohead dhtnn) tmgraph;
val s = reall_to_string embed1;
val embed2 = time string_to_reall s;
*)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term
fun apply_move move (ctxt,tm) = (ctxt, apply_move_aux move tm)
fun available_move board move = available_move_aux (snd board) move
fun string_of_move move = tts move

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  board_compare = board_compare,
  string_of_board = string_of_board,
  movel = movel,
  move_compare = Term.compare,
  string_of_move = string_of_move,
  status_of = status_of,
  available_move = available_move,
  apply_move = apply_move
  }

(* -------------------------------------------------------------------------
   Big steps limit (redundant with status_of)
   ------------------------------------------------------------------------- *)

fun max_bigsteps ((orgtm,_),_) = 2 * term_size orgtm + 10

(* -------------------------------------------------------------------------
   Levels
   ------------------------------------------------------------------------- *)

val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"

val train_file = datasetsynt_dir ^ "/train_lisp"

fun bin_to_string bin = String.concatWith "," (map its bin)

fun create_levels () =
  let
    val formgraphl = parse_setsyntdata ()
    val _ = print_endline ("Reading " ^ its (length formgraphl) ^ " terms");
    val l1 = map (fn (a,b) => (a ,rev b)) formgraphl
    val l2 = mapfilter (fn x => (x, valOf (eval64 (fst x)))) l1
    fun f ((a,b),c) =
      if b = c then () else
        (
        print_endline (bin_to_string b);
        print_endline (bin_to_string c);
        raise ERR "not_equal_on" (term_to_string a)
        )
    val _ = app f l2
    val tml = map (fst o fst) l2
    fun g tm =
      if can imitate tm then () else
        raise ERR "cannot replicate" (term_to_string tm)
    val _ = app g tml
  in
    print_endline ("Exporting " ^ its (length tml) ^ " terms");
    export_terml (datasetsynt_dir ^ "/h4setsynt")
      (dict_sort tmsize_compare tml)
  end

fun level_targetl level ntarget =
  let
    val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt")
    val tmll2 = map shuffle (first_n level (mk_batch_full 400 tml1))
    val tml3 = List.concat (list_combine tmll2)
    val tml4 = rev (dict_sort tmsize_compare (first_n ntarget tml3))
  in
    map mk_startboard tml4
  end

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_target file target =
  export_terml (file ^ "_target") [dest_startboard target]
fun read_target file =
  mk_startboard (only_hd (import_terml (file ^ "_target")))

fun write_exl file exl =
  let
    val (boardl,evall,polil) = split_triple exl
    val (l1,l2) = split boardl
    val (l1a,l1b) = split l1
  in
    export_terml (file ^ "_orgtm") l1a;
    writel (file ^ "_graph") (map string_of_graph l1b);
    export_terml (file ^ "_conttm") l2;
    writel (file ^ "_eval") (map reall_to_string evall);
    writel (file ^ "_poli") (map reall_to_string polil)
  end
fun read_exl file =
  let
    val orgl = import_terml (file ^ "_orgtm")
    val graphl = map graph_of_string (readl (file ^ "_graph"))
    val contl = import_terml (file ^ "_conttm")
    val evall = map string_to_reall (readl (file ^ "_eval"))
    val polil = map string_to_reall (readl (file ^ "_poli"))
    val boardl = combine (combine (orgl,graphl), contl)
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
   Players
   ------------------------------------------------------------------------- *)

val schedule_base =
  [{ncore = 4, verbose = true,
    learning_rate = 0.02,
    batch_size = 16, nepoch = 25}]
val dhtnn_param_base =
  {
  operl = operl1, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 12, dimpoli = length movel
  }
val player_base =
  {playerid = "base",
   dhtnn_param = dhtnn_param_base, schedule = schedule_base}

(*
val schedule_4core =
  [{ncore = 4, verbose = true,
    learning_rate = 0.02,
    batch_size = 16, nepoch = 200}]
val player_4core =
  {playerid = "4core",
   dhtnn_param = dhtnn_param_base, schedule = schedule_4core}

val schedule_100epoch =
  [{ncore = 4, verbose = true,
    learning_rate = 0.02,
    batch_size = 16, nepoch = 100}]
val player_100epoch =
  {playerid = "100epoch",
   dhtnn_param = dhtnn_param_base, schedule = schedule_100epoch}

val schedule_4batch =
  [{ncore = 4, verbose = true,
    learning_rate = 0.01,
    batch_size = 4, nepoch = 200}]
val player_4batch =
  {playerid = "4batch",
   dhtnn_param = dhtnn_param_base, schedule = schedule_4batch}

val dhtnn_param_1layer =
  {
  operl = operl1, nlayer_oper = 1,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 12, dimpoli = length movel
  }
val player_1layer =
  {playerid = "1layer",
   dhtnn_param = dhtnn_param_base, schedule = schedule_base}

val dhtnn_param_quantterm =
  {
  operl = operl2, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 12, dimpoli = length movel
  }
val player_quantterm =
  {playerid = "quantterm",
   dhtnn_param = dhtnn_param_quantterm ,
   schedule = schedule_base}

val dhtnn_param_listgraph =
  {
  operl = operl3, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 12, dimpoli = length movel
  }
val player_listgraph =
  {playerid = "listgraph",
   dhtnn_param = dhtnn_param_listgraph,
   schedule = schedule_base}

val dhtnn_param_allgraph =
  {
  operl = operl4, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 12, dimpoli = length movel
  }
val player_allgraph =
  {playerid = "allgraph",
   dhtnn_param = dhtnn_param_allgraph,
   schedule = schedule_base}
*)

val tobdict = dnew String.compare
  [("base", term_of_board1 (#dimin dhtnn_param_base))]

fun mk_graphv dim dhtnn ((_,graph),_) = 
  let 
    val tmgraph = term_of_graph dim graph
    val embed1 = infer_dhtnn_nohead dhtnn tmgraph
    val s = reall_to_string embed1
  in
    mk_var (embedding_prefix ^ s,bool)
  end
 
fun term_of_board1p graphv ((_,_),tm) =
  list_mk_comb (adjgraph, [graphv, rw_to_uncont tm])

val tobpdict = dnew String.compare
  [("base", (term_of_board1p, mk_graphv (#dimin dhtnn_param_base))]


(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val expname = "mleSetSynt-v2-13"

val level_param =
  {
  ntarget_start = 400, ntarget_compete = 400, ntarget_explore = 400,
  level_start = 1, level_threshold = 0.75,
  level_targetl = level_targetl
  }

val rl_param =
  {
  expname = expname, ex_window = 160000, ex_filter = NONE,
  ngen = 400, ncore_search = 40,
  nsim_start = 32000, nsim_explore = 32000, nsim_compete = 32000,
  decay = 1.0
  }

val rlpreobj : (board,move) rlpreobj =
  {
  rl_param = rl_param,
  level_param = level_param,
  max_bigsteps = max_bigsteps,
  game = game,
  pre_extsearch = pre_extsearch,
  tobdict = tobdict,
  dplayerl = [player_base]
  }

val extsearch = mk_extsearch "mleSetSynt.extsearch" rlpreobj

val rlobj = mk_rlobj rlpreobj extsearch

(* -------------------------------------------------------------------------
   Reinforcement learning
   ------------------------------------------------------------------------- *)

(*
load "mlReinforce"; open mlReinforce;
load "mleSetSynt"; open mleSetSynt;
(* create_levels (); *)
val r = start_rl_loop rlobj;
*)

(* -------------------------------------------------------------------------
   MCTS test with uniform player
   ------------------------------------------------------------------------- *)

(*
load "mleSetSynt"; open mleSetSynt;
load "psMCTS"; open psMCTS;
load "aiLib"; open aiLib;
load "mlTacticData"; open mlTacticData;

val mcts_param =
  {
  nsim = 100000,
  stopatwin_flag = true,
  decay = #decay (#rl_param rlpreobj),
  explo_coeff = 2.0,
  noise_flag = false, noise_coeff = 0.25, noise_alpha = 0.2
  };

val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"
val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt");
val targetl1 = map mk_startboard (first_n 100 tml1);

fun test i target =
  let 
    val mcts_obj =
      {cuttree = NONE, mcts_param = mcts_param,
       game = #game rlpreobj, player = uniform_player (#game rlpreobj)}
    val tree = starttree_of mcts_obj target
    val endtree = mcts mcts_obj tree
  in
    print_endline (its i);
    #status (dfind [] endtree) = Win
  end

val targetl2 = combine (targetl1, mapi test targetl1);
val targetl3 = filter snd targetl2;
length targetl3;
*)



end (* struct *)
