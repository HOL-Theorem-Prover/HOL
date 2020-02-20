(* ========================================================================= *)
(* FILE          : mleDiophSynt.sml                                          *)
(* DESCRIPTION   : Specification of term synthesis on Diophantine equations  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleDiophSynt :> mleDiophSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce arithmeticTheory numLib numSyntax mleDiophLib

val ERR = mk_HOL_ERR "mleDiophSynt"
val version = 2
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = int list list * bool list * int
fun string_of_board (a,b,c)=
  poly_to_string a ^ " -- " ^ graph_to_string b ^ " -- " ^ its c

fun board_compare ((a,b,c),(d,e,f)) =
  cpl_compare poly_compare graph_compare ((a,b),(d,e))

fun fullboard_compare ((a,b,c),(d,e,f)) =
  triple_compare Int.compare poly_compare graph_compare ((c,a,b),(f,d,e))

fun status_of (poly,graph,n) =
  if dioph_match poly graph then Win
  else if n <= 0 then Lose
  else Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Add of int | Exp of int
val movel = map Add numberl @ map Exp (List.tabulate (maxexponent + 1, I))

fun string_of_move move = case move of
    Add i => "A" ^ its i
  | Exp i => "E" ^ its i

fun move_compare (a,b) = String.compare (string_of_move a, string_of_move b)

fun apply_move_poly move poly =
  case move of
    Add c => if length poly >= maxmonomial
             then raise ERR "apply_move_poly" "plus"
             else poly @ [[c]]
  | Exp c => if null poly orelse length (last poly) >= maxvar + 1
               then raise ERR "apply_move_poly" "mult"
             else if length poly >= 2 andalso
               let
                 val prevexp = tl (last (butlast poly))
                 val curexp = tl (last poly) @ [c]
                 val m = Int.min (length curexp,length prevexp)
               in
                 list_compare Int.compare (first_n m prevexp, first_n m curexp)
                 = GREATER
               end
             then raise ERR "apply_move_poly" "non-increasing"
             else butlast poly @ [last poly @ [c]]

fun apply_move move (poly,graph,n) = (apply_move_poly move poly, graph, n-1)

fun available_movel_poly poly =
  filter (fn x => can (apply_move_poly x) poly) movel

fun available_movel (poly,_,_) = available_movel_poly poly

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  apply_move = apply_move,
  available_movel = available_movel,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movel
  }

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let val (l1,l2,l3) = split_triple boardl in
    writel (file ^ "_poly") (map poly_to_string l1);
    writel (file ^ "_graph") (map graph_to_string l2);
    writel (file ^ "_timer") (map its l3)
  end

fun read_boardl file =
  let
    val l1 = map string_to_poly (readl_empty (file ^ "_poly"))
    val l2 = map string_to_graph (readl (file ^ "_graph"))
    val l3 = map string_to_int (readl (file ^ "_timer"))
  in
    combine_triple (l1,l2,l3)
  end

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/dioph_target"

fun graph_to_bl graph = map (fn x => mem x graph) numberl

fun create_targetl l =
  let
    val (train,test) = part_pct (10.0/11.0) (shuffle l)
    val _ = export_data (train,test)
    fun f (graph,poly) = ([], graph_to_bl graph, 2 * poly_size poly)
  in
    (dict_sort fullboard_compare (map f train),
     dict_sort fullboard_compare (map f test))
  end

fun export_targetl name targetl =
  let val _ = mkDir_err targetdir in
    write_boardl (targetdir ^ "/" ^ name) targetl
  end

fun import_targetl name = read_boardl (targetdir ^ "/" ^ name)

fun mk_targetd l1 =
  let
    val l2 = number_snd 0 l1
    val l3 = map (fn (x,i) => (x,(i,[]))) l2
  in
    dnew board_compare l3
  end

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

fun term_of_graph graph =
  mk_embedding_var
  (Vector.fromList (map (fn x => if x then 1.0 else ~1.0) graph), bool)

val head_eval = mk_var ("head_eval", ``:bool -> 'a``)
val head_poli = mk_var ("head_poli", ``:bool -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)
val graph_tag = mk_var ("graph_tag", ``:bool -> num``)
fun tag_graph x = mk_comb (graph_tag,x)

fun tob1 (poly,graph,_) =
  let
    val (tm1,tm2) = (term_of_poly poly, tag_graph (term_of_graph graph))
    val tm = mk_eq (tm1,tm2)
  in
    [tag_heval tm, tag_hpoli tm]
  end

fun tob2 embedv (poly,_,_) =
  let
    val (tm1,tm2) = (term_of_poly poly, embedv)
    val tm = mk_eq (tm1,tm2)
  in
    [tag_heval tm, tag_hpoli tm]
  end

fun pretob boardtnno = case boardtnno of
    NONE => tob1
  | SOME ((_,graph,_),tnn) =>
    tob2 (precomp_embed tnn (tag_graph (term_of_graph graph)))

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10}]

val dioph_operl =
  [``$= : num -> num -> bool``,
   graph_tag,``$+``,``$*``,mk_var ("start",``:num``)] @
  map (fn i => mk_var ("n" ^ its i,``:num``)) numberl @
  List.concat
    (List.tabulate (maxvar, fn v =>
     List.tabulate (maxexponent + 1, fn p =>
       mk_var ("v" ^ its v ^ "p" ^ its p,``:num``))))

val dim = 16
fun dim_head_poli n = [dim,n]

val tnnparam = map_assoc (dim_std (1,dim)) dioph_operl @
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]
val dplayer = {pretob = pretob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleDiophSynt-" ^ its version, exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer}

val extsearch = mk_extsearch "mleDiophSynt.extsearch" rlobj

(* -------------------------------------------------------------------------
   Final test
   ------------------------------------------------------------------------- *)

val ft_extsearch_uniform =
  ft_mk_extsearch "mleDiophSynt.ft_extsearch_uniform" rlobj
    (uniform_player game)

fun graph_distance bl1 bl2 =
  let
    val bbl1 = combine (bl1,bl2)
    val bbl2 = filter (fn (a,b) => a = b) bbl1
  in
    int_div (length bbl2) (length bl1)
  end

fun distance_player (board as (poly,set,_)) =
  let
    val e = if null poly
            then 0.0
            else graph_distance (graph_to_bl (dioph_set poly)) set
  in
    (e, map (fn x => (x,1.0)) (available_movel board))
  end

val ft_extsearch_distance =
  ft_mk_extsearch "mleDiophSynt.ft_extsearch_distance" rlobj distance_player

val fttnn_extsearch =
  fttnn_mk_extsearch "mleDiophSynt.fttnn_extsearch" rlobj

val fttnnbs_extsearch =
  fttnnbs_mk_extsearch "mleDiophSynt.fttnnbs_extsearch" rlobj

(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleDiophLib"; open mleDiophLib;
load "mleDiophSynt"; open mleDiophSynt;

val (dfull,ntry) = gen_diophset 0 2200 (dempty (list_compare Int.compare));
val (train,test) = create_targetl (dlist dfull); length train; length test;
val _ = (export_targetl "train" train; export_targetl "test" test);
val targetl = import_targetl "train"; length targetl;
val _ = rl_start (rlobj,extsearch) (mk_targetd targetl);

val targetd = retrieve_targetd rlobj 75;
val _ = rl_restart 75 (rlobj,extsearch) targetd;
*)

(* -------------------------------------------------------------------------
   MCTS test for inspection of the results
   ------------------------------------------------------------------------- *)

fun solve_target (unib,tim,tnn) target =
  let
    val mctsparam =
    {
    timer = SOME tim,
    nsim = (NONE : int option),
    stopatwin_flag = true,
    decay = 1.0,
    explo_coeff = 2.0,
    noise_all = false,
    noise_root = false,
    noise_coeff = 0.25,
    noise_gen = random_real,
    noconfl = false,
    avoidlose = false
    }
  val pretob = (#pretob (#dplayer rlobj));
  fun preplayer target =
    let val tob = pretob (SOME (target,tnn)) in
      fn board => mlReinforce.player_from_tnn tnn tob (#game rlobj) board
    end;
  val mctsobj =
    {mctsparam = mctsparam, game = #game rlobj,
     player = if unib then uniform_player (#game rlobj) else preplayer target}
  in
    fst (mcts mctsobj (starttree_of mctsobj target))
  end

fun solve_diophset (unib,tim,tnn) diophset =
  let
    val target = ([]:poly,graph_to_bl diophset,40);
    val tree = solve_target (unib,tim,tnn) target;
    val b = #status (dfind [] tree) = Win;
  in
    if b then
      let val nodel = trace_win tree [] in
        print_endline (its (dlength tree));
        print_endline (human_of_poly (#1 (#board (last nodel))))
      end
    else
      (print_endline (its (dlength tree)); print_endline "Time out")
  end

(*
load "aiLib"; open aiLib;
load "mleDiophSynt"; open mleDiophSynt;
val tnn = mlReinforce.retrieve_tnn rlobj 197;
val diophset = [1,3];
solve_diophset_uniform diophset;
solve_diophset diophset;
*)

(* -------------------------------------------------------------------------
   Final testing
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "smlParallel"; open smlParallel;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleDiophSynt"; open mleDiophSynt;

val dir1 = HOLDIR ^ "/examples/AI_tasks/dioph_results_nolimit";
val _ = mkDir_err dir1;
fun store_result dir (a,i) =
  #write_result ft_extsearch_uniform (dir ^ "/" ^ its i) a;

(*** Testing set ***)
val dataset = "test";
val pretargetl = import_targetl dataset;
val targetl = map (fn (a,b,_) => (a,b,1000000)) pretargetl;
length targetl;
(* uniform *)
val (l1',t) = add_time (parmap_queue_extern 20 ft_extsearch_uniform ()) targetl;
val winb = filter I (map #1 l1'); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_uniform";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l1');
(* distance *)
val (l2',t) =
  add_time (parmap_queue_extern 20 ft_extsearch_distance ()) targetl;
val winb = filter I (map #1 l2'); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_distance";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l2');
(* tnn *)
val tnn = mlReinforce.retrieve_tnn rlobj 197;
val (l3',t) = add_time (parmap_queue_extern 20 fttnn_extsearch tnn) targetl;
val winb = filter I (map #1 l3'); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_tnn";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l3');

(*** Training set ***)
val dataset = "train";
val pretargetl = import_targetl dataset;
val targetl = map (fn (a,b,_) => (a,b,1000000)) pretargetl;
length targetl;
(* uniform *)
val (l1,t) = add_time (parmap_queue_extern 20 ft_extsearch_uniform ()) targetl;
val winb = filter I (map #1 l1); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_uniform";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l1);
(* distance *)
val (l2,t) =
  add_time (parmap_queue_extern 20 ft_extsearch_distance ()) targetl;
val winb = filter I (map #1 l2); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_distance";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l2);
(* tnn *)
val tnn = mlReinforce.retrieve_tnn rlobj 197;
val (l3,t) = add_time (parmap_queue_extern 20 fttnn_extsearch tnn) targetl;
val winb = filter I (map #1 l3); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_tnn";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l3);
*)

(* -------------------------------------------------------------------------
   Final testing statistics
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "smlParallel"; open smlParallel;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleDiophSynt"; open mleDiophSynt;

val dir2 = HOLDIR ^ "/examples/AI_tasks/dioph_results/test_uniform";
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val l1 = List.tabulate (10,g);
val l2 = filter #1 l1;
val l3 = map (valOf o #3) l2;
val l4 = map (fn (a,b,c) => (a,b)) l3;
mleDiophLib.dioph_set (fst (hd l4));
*)

end (* struct *)
