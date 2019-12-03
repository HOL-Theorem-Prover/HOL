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
  cpl_compare Term.compare Term.compare ((a,c),(d,f))

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
   Term representations of the board
   ------------------------------------------------------------------------- *)

val graphtag = mk_var ("graphtag", ``:bool -> bool``)

fun string_of_graph graph =
  String.concatWith " " (map bts graph)
fun graph_of_string s =
  map string_to_bool (String.tokens Char.isSpace s)

fun embed_of_graph graph =
  Vector.fromList (map (fn x => if x then 1.0 else ~1.0) graph)

fun term_of_graph dim graph =
  let
    val graphl = mk_batch_full dim graph
    val bl = map embed_of_graph (butlast graphl)
    val b1 = embed_of_graph (last graphl)
    val b2 = Vector.concat [b1,
      Vector.tabulate (dim - Vector.length b1, fn _ => 0.0)]
    val varl = map mk_embedding_var (bl @ [b2])
  in
    list_mk_binop graphcat varl
  end

fun term_of_board1 dim ((_,graph),tm) =
  list_mk_comb (adjgraph, [term_of_graph dim graph, rw_to_uncont tm])

val operl1 = mk_fast_set oper_compare
  (map_assoc arity_of (graphcat :: adjgraph :: (uncontl @ operl_plain)))

fun mk_graphv dim dhtnn ((_,graph),_) =
  let
    val tmgraph = term_of_graph dim graph
    val embed = infer_dhtnn_nohead dhtnn tmgraph
  in
    mk_embedding_var embed
  end

fun term_of_board1c graphv ((_,_),tm) =
  list_mk_comb (adjgraph, [graphv, rw_to_uncont tm])

(* -------------------------------------------------------------------------
   Masking the graph
   ------------------------------------------------------------------------- *)

fun mask_graph graph =
  Vector.fromList (map (fn x => 0.0) graph)

fun mask_graphtm dim graph =
  let
    val graphl = mk_batch_full dim graph
    val bl = map mask_graph (butlast graphl)
    val b1 = mask_graph (last graphl)
    val b2 = Vector.concat [b1,
      Vector.tabulate (dim - Vector.length b1, fn _ => 0.0)]
    val varl = map mk_embedding_var (bl @ [b2])
  in
    list_mk_binop graphcat varl
  end

fun mask_graphv dim dhtnn ((_,graph),_) =
  let
    val tmgraph = mask_graphtm dim graph
    val embed = infer_dhtnn_nohead dhtnn tmgraph
  in
    mk_embedding_var embed
  end

(*
load "aiLib"; open aiLib;
load "mleSetLib"; open mleSetLib;
load "mleSetSynt"; open mleSetSynt;

val l1 = parse_setsyntdata ();
val tml = map fst l1;
val graph = List.tabulate (64,fn _ => false);
val board : board = ((F,graph), random_elem tml);
val tm1 = term_of_board1 8 board;
val tm2 = term_of_graph 8 graph;
val tm3 = mask_graphtm 8 graph;
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
   Initialization of the levels
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

fun level_targetl level =
  let 
    val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt") 
    val tmll = map shuffle (first_n level (mk_batch 400 tml1))
    val tml2 = first_n 400 (List.concat (list_combine tmll))
    val tml3 = rev (dict_sort tmsize_compare tml2)
  in
    map mk_startboard tml3
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
    writel (file ^ "_graph") (map string_of_graph l1b);
    export_terml (file ^ "_conttm") l2
  end
fun read_boardl file =
  let
    val orgl = import_terml (file ^ "_orgtm")
    val graphl = map graph_of_string (readl (file ^ "_graph"))
    val contl = import_terml (file ^ "_conttm")
  in
    combine (combine (orgl,graphl), contl)
  end

fun write_exl file exl =
  let val (boardl,evall,polil) = split_triple exl in
    write_boardl file boardl;
    writel (file ^ "_eval") (map reall_to_string evall);
    writel (file ^ "_poli") (map reall_to_string polil)
  end
fun read_exl file =
  let
    val boardl = read_boardl file
    val evall = map string_to_reall (readl (file ^ "_eval"))
    val polil = map string_to_reall (readl (file ^ "_poli"))
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
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]
val dhtnn_param_base =
  {
  operl = operl1, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 8, dimpoli = length movel
  }
val player_base =
  {playerid = "base",
   dhtnn_param = dhtnn_param_base, schedule = schedule_base}

val pretobdict = dnew String.compare
  [("base", (term_of_board1 (#dimin dhtnn_param_base), term_of_board1c))]

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val expname = "mleSetSynt-test1"

val rl_param =
  {
  expname = expname, ex_window = 200000,
  ncore_search = 40, nsim = 50000, decay = 1.0
  }

val rlpreobj : (board,move,term) rlpreobj =
  {
  rl_param = rl_param,
  max_bigsteps = max_bigsteps,
  game = game,
  pre_extsearch = pre_extsearch,
  pretobdict = pretobdict,
  precomp_dhtnn = mk_graphv (#dimin dhtnn_param_base),
  dplayerl = [player_base],
  level_targetl = level_targetl
  }


val extsearch = mk_extsearch "mleSetSynt.extsearch" rlpreobj
val rlobj = mk_rlobj rlpreobj extsearch


val rlpreobj_mask : (board,move,term) rlpreobj =
  {
  rl_param = rl_param,
  max_bigsteps = max_bigsteps,
  game = game,
  pre_extsearch = pre_extsearch,
  pretobdict = pretobdict,
  precomp_dhtnn = mask_graphv (#dimin dhtnn_param_base),
  dplayerl = [player_base],
  level_targetl = level_targetl
  }

val extsearch_mask = mk_extsearch "mleSetSynt.extsearch_mask" rlpreobj_mask
val rlobj_mask = mk_rlobj rlpreobj_mask extsearch_mask

(* -------------------------------------------------------------------------
   Reinforcement learning
   ------------------------------------------------------------------------- *)

(*
load "mlReinforce"; open mlReinforce;
load "mleSetSynt"; open mleSetSynt;
(* create_levels (); *)
val _ = rl_restart_sync rlobj ((131,131),2);
*)

(* -------------------------------------------------------------------------
   Test without noise
   ------------------------------------------------------------------------- *)

(*
load "mlReinforce"; open mlReinforce;
load "mleSetSynt"; open mleSetSynt;
load "aiLib"; open aiLib;
load "mlTacticData"; open mlTacticData;
(* create_levels (); *)

val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"
val tml = import_terml (datasetsynt_dir ^ "/h4setsynt");
val targetl = map mk_startboard (first_n 1200 tml);
val (targetl1,targetl2,targetl3) = triple_of_list 
  (map rev (mk_batch 400 targetl));
map length [targetl1,targetl2,targetl3];

val rplayer = retrieve_player rlobj 148;

val _ = log rlobj "\n Breadth-first";
val _ = log rlobj "Level 1";
val _ = explore_standalone (true,false) rlobj rplayer targetl1;
val _ = log rlobj "Level 2";
val _ = explore_standalone (true,false) rlobj rplayer targetl2;
val _ = log rlobj "Level 3";
val _ = explore_standalone (true,false) rlobj rplayer targetl3;

val _ = log rlobj "\n Hidden-graph";
val _ = log rlobj "Level 1";
val _ = explore_standalone (false,false) rlobj_mask rplayer targetl1;
val _ = log rlobj "Level 2";
val _ = explore_standalone (false,false) rlobj_mask rplayer targetl2;
val _ = log rlobj "Level 3";
val _ = explore_standalone (false,false) rlobj_mask rplayer targetl3;

val _ = log rlobj "\n Guided";
val _ = log rlobj "Level 1";
val _ = explore_standalone (false,false) rlobj rplayer targetl1;
val _ = log rlobj "Level 2";
val _ = explore_standalone (false,false) rlobj rplayer targetl2;
val _ = log rlobj "Level 3";
val _ = explore_standalone (false,false) rlobj rplayer targetl3;
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
  nsim = 50000,
  stopatwin_flag = true,
  decay = #decay (#rl_param rlpreobj),
  explo_coeff = 2.0,
  noise_coeff = 0.25,
  noise_gen = 0.2
  };

val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"
val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt");
val targetl1 = map mk_startboard (first_n 100 tml1);
val graphl = map (snd o fst) targetl1;
val graph_set = mk_fast_set (list_compare bool_compare) graphl;
length graph_set;

fun test i target =
  let
    val mcts_obj =
      {mcts_param = mcts_param,
       game = #game rlpreobj,
       player = uniform_player (#game rlpreobj)}
    val tree = starttree_of mcts_obj target
    val endtree = mcts mcts_obj tree
  in
    print_endline (its i);
    #status (dfind [] endtree) = Win
  end
;

val targetl2 = combine (targetl1, mapi test targetl1);
val targetl3 = filter snd targetl2;
length targetl3;
*)

(* -------------------------------------------------------------------------
   Big steps test
   ------------------------------------------------------------------------- *)

(*
load "mleSetSynt"; open mleSetSynt;
load "psMCTS"; open psMCTS;
load "psBigSteps"; open psBigSteps;
load "aiLib"; open aiLib;
load "mlTacticData"; open mlTacticData;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

(* player *)
val eval_dir = HOLDIR ^ "/src/AI/experiments/eval";
fun player_file n =
  eval_dir ^ "/" ^ (#expname (#rl_param rlobj)) ^ "/player" ^ its n;
fun retrieve_player n =
  (
  read_dhtnn (player_file n ^ "_dhtnn"),   
  only_hd (readl (player_file n ^ "_id"))     
  );
val (dhtnn,playerid) = retrieve_player 148;

(* target *)
val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt";
val tml = import_terml (datasetsynt_dir ^ "/h4setsynt");
val target = mk_startboard (List.nth (tml,112));

(* bigsteps *)
fun player_from_dhtnn (tobc,dhtnn) ctxt board =
   let val (e,p) = infer_dhtnn dhtnn (tobc ctxt board) in
     (e, combine (#movel (#game rlpreobj),p))
   end;

fun mk_mcts_param noiseb nsim =
  {
  nsim = nsim,
  stopatwin_flag = false,
  decay = #decay (#rl_param rlpreobj),
  explo_coeff = 2.0,
  noise_all = noiseb,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real
  };

fun mk_bigsteps_obj (dhtnn,noiseb,playerid,nsim) =
  let
    val game = #game rlpreobj
    val (tob,tobc) = dfind playerid (#pretobdict rlpreobj)
    fun preplayer ctxt board = player_from_dhtnn (tobc,dhtnn) ctxt board
    fun precomp board = (#precomp_dhtnn rlpreobj) dhtnn board
  in
    {
    verbose = true,
    temp_flag = false,
    max_bigsteps = #max_bigsteps rlpreobj,
    precomp = precomp,
    preplayer = preplayer,
    game = game,
    mcts_param = mk_mcts_param noiseb nsim
    }
  end;

val bigsteps_obj = mk_bigsteps_obj (dhtnn,true,playerid,50000);
val _ = run_bigsteps bigsteps_obj target;
*)  


end (* struct *)
