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
val selfdir = HOLDIR ^ "/examples/AI/RL/diophantine"

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

fun apply_move move (poly,graph,n) =
  (apply_move_poly move poly, graph, n-1)

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
  if null graph then raise ERR "term_of_graph" "empty" else
  list_mk_conj (map (fn x => if x then T else F) graph)

val head_eval = mk_var ("head_eval", ``:bool -> 'a``)
val head_poli = mk_var ("head_poli", ``:bool -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)
val graph_tag = mk_var ("graph_tag", ``:bool -> num``)
fun tag_graph x = mk_comb (graph_tag,x)

fun term_of_board (poly,graph,_) =
  mk_eq (term_of_poly poly, tag_graph (term_of_graph graph))

fun tob board =
  let val tm = term_of_board board in
    [tag_heval tm, tag_hpoli tm]
  end

fun player_from_tnn tnn board =
  let
    val boardemb = infer_emb tnn (term_of_board board)
    val e = descale_out (fp_emb tnn head_eval [boardemb])
    val p = descale_out (fp_emb tnn head_poli [boardemb])
    val d = dnew move_compare (combine (movel,p))
    fun f x = dfind x d handle NotFound => raise ERR "player_from_tnn" ""
  in
    (singleton_of_list e, map_assoc f (available_movel board))
  end

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10}]

val dioph_operl =
  [``$= : num -> num -> bool``,``$/\ : bool -> bool -> bool``,
   graph_tag,``$+``,``$*``,mk_var ("start",``:num``)] @
  map (fn i => mk_var ("n" ^ its i,``:num``)) numberl @
  List.concat
    (List.tabulate (maxvar, fn v =>
     List.tabulate (maxexponent + 1, fn p =>
       mk_var ("v" ^ its v ^ "p" ^ its p,``:num``))))

val dim = 16
fun dim_head_poli n = [dim,n]

val tnndim = map_assoc (dim_std (1,dim)) dioph_operl @
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]

val dplayer = {player_from_tnn = player_from_tnn,
  tob = tob, tnndim = tnndim, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expdir = (mkDir_err (selfdir ^ "/eval");
             selfdir ^ "/eval/dioph-" ^ its version),
   exwindow = 200000, ncore = 30, ntarget = 200, nsim = 32000}

val rlobj: (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer,
   infobs = fn _ => ()}

val extsearch = mk_extsearch selfdir "mleDiophSynt.extsearch" rlobj

(* -------------------------------------------------------------------------
   Training run
   ------------------------------------------------------------------------- *)

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

end (* struct *)
