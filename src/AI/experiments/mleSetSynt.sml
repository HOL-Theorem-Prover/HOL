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
   Helper
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

val graph_size = 64

fun mk_graph n t =
  map (eval_subst (xvar,t) o nat_to_bin) (List.tabulate (n,I))

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = ((term * bool list) * term)

val board_compare =
  cpl_compare
    (cpl_compare Term.compare (list_compare bool_compare))
    Term.compare

fun string_of_board ((_,bl),tm) =
  String.concatWith " " (map bts bl) ^ " :\n" ^ tts tm

fun mk_graph n t =
  map (eval_subst (xvar,t) o nat_to_bin) (List.tabulate (n,I))

fun mk_startboard tm = ((tm,mk_graph graph_size tm),start_form)
fun dest_startboard ((tm,_),_) = tm

fun status_of ((orgtm,graph),tm) =
  if not (can (find_term is_cont) tm) then
    if graph = mk_graph graph_size tm handle HOL_ERR _ => false
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
  else raise ERR "numvar_of_graph" 
    "dimension of the graph not a multiple of the dimension of the network"

fun term_of_graph dim graph =
  let 
    val graphl = mk_batch_full dim graph
    val numvarl = map (numvar_of_graph dim) graphl
  in
    list_mk_binop graphcat numvarl
  end

fun term_of_board1 dim ((_,graph),tm) =
  list_mk_comb (adjgraph, [term_of_graph dim graph, rw_to_uncont tm])

val operl1 = mk_fast_set oper_compare
  (map_assoc arity_of (graphcat :: adjgraph :: (uncontl @ operl_plain)))

(* -------------------------------------------------------------------------
   2) Annotate operators with number of quantifiers above them
   ------------------------------------------------------------------------- *)

fun is_numvar v = String.isPrefix tnn_numvar_prefix (fst (dest_var v))

fun annotate_var n v =
  if tmem v yvarl then v else
  let val (vs,ty) = dest_var v in mk_var (vs ^ "_" ^ its n, ty) end

fun all_annot v =
  if tmem v yvarl then [v]
  else List.tabulate (max_quants + 1, fn n => annotate_var n v)

fun ind_quant n tm =
  let val (oper,argl) = strip_comb tm in
    if tmem oper quantl then
      let
        val (v,bound,bod) = triple_of_list argl
        val bound' = ind_quant n bound
        val bod' = ind_quant (n+1) bod
      in
        list_mk_comb (annotate_var n oper,[v,bound',bod'])
      end
    else list_mk_comb (annotate_var n oper, map (ind_quant n) argl)
  end

fun term_of_board2 dim ((_,graph),tm) =
  list_mk_comb (adjgraph, [term_of_graph dim graph,
    ind_quant 0 (rw_to_uncont tm)])

val operl2 = mk_fast_set oper_compare
  (map_assoc arity_of (
   graphcat :: adjgraph ::
   List.concat (map all_annot (uncontl @ operl_plain))))

(* -------------------------------------------------------------------------
   3) Graph represented by a list
   ------------------------------------------------------------------------- *)

fun booltermlist_of_graph graph =
  let val l = map (fn x => if x then T else F) graph in
    list_mk_binop graphcat l
  end

fun term_of_board3 ((_,graph),tm) =
  list_mk_comb (adjgraph, [booltermlist_of_graph graph, rw_to_uncont tm])

val operl3 = mk_fast_set oper_compare
  (map_assoc arity_of
     (T :: F :: graphcat :: adjgraph :: (uncontl @ operl_plain)));

(* -------------------------------------------------------------------------
   3) graph as argument of all nodes (expensive)
   ------------------------------------------------------------------------- *)

fun extend_var v =
  let val (vs,ty) = dest_var v in
    mk_var (vs ^ "_ext", mk_type ("fun", [bool,ty]))
  end

fun add_graph numvar tm =
  let val (oper,argl) = strip_comb tm in
    list_mk_comb (extend_var oper, numvar :: map (add_graph numvar) argl)
  end

fun term_of_board4 dim ((_,graph),tm) =
  add_graph (term_of_graph dim graph) (rw_to_uncont tm)

val operl4 = mk_fast_set oper_compare
  (map_assoc arity_of (graphcat :: map extend_var (uncontl @ operl_plain)));

(*
load "aiLib"; open aiLib;
load "mleSetLib"; open mleSetLib;
load "mleSetSynt"; open mleSetSynt;
val l1 = parse_setsyntdata ();
val tml = map fst l1;
val board : board = ((T,List.tabulate (64,fn _ => false)), random_elem tml);
val tm1 = term_of_board1 board;
val tm2 = term_of_board2 board;
val tm3 = term_of_board3 board;
val tm4 = term_of_board4 board;
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

fun eval64 t =
  let
    val l = List.tabulate (64,I)
    fun f x = (eval_subst (xvar,t) (nat_to_bin x), x)
  in
    map snd (filter fst (map f l))
  end
  handle HOL_ERR _ => raise ERR "eval64" (term_to_string t)

fun bin_to_string bin = String.concatWith "," (map its bin)

fun export_setsyntdata () =
  let
    val formgraphl = parse_setsyntdata ()
    val _ = print_endline ("Reading " ^ its (length formgraphl) ^ " terms");
    val l1 = map (fn (a,b) => (a ,rev b)) formgraphl
    val l2 = map_assoc (eval64 o fst) l1
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
  in
    map mk_startboard (first_n ntarget tml3)
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
  dimin = 8, dimpoli = length movel
  }
val player_base =
  {playerid = "base",
   dhtnn_param = dhtnn_param_base, schedule = schedule_base}

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

val tobdict = dnew String.compare
  [
  ("base",term_of_board1 8),
  ("4core",term_of_board1 8),
  ("100epoch",term_of_board1 8),
  ("4batch",term_of_board1 8),
  ("1layer",term_of_board1 8),
  ("quantterm",term_of_board2 8),
  ("listgraph",term_of_board3),
  ("allgraph",term_of_board4 8)
  ];

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
  ngen = 400, ncore_search = 45,
  nsim_start = 32000, nsim_explore = 32000, nsim_compete = 32000,
  decay = 0.99
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
(* export_setsyntdata (); *)
val r = start_rl_loop rlobj;
*)

end (* struct *)
