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
  mlReinforce mleLib mleArithData combinTheory

val ERR = mk_HOL_ERR "mleRewrite"

val tmsize_limit = 200
val version = 14

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = term * term * int

fun string_of_board (a,b,c) = cts a ^ "\n" ^ cts b ^ "\n" ^ its c
fun board_compare ((a,b,_),(c,d,_)) = 
  cpl_compare Term.compare Term.compare ((a,b),(c,d))

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term
val movel = [s_thm_tagged,k_thm_tagged,left_thm,right_thm]

fun string_of_move eq = tts eq

fun add_tag eq tm =
  if tmem eq [k_thm_tagged,s_thm_tagged] then tag tm else tm

fun apply_move eq (tm1,tm2,n) = 
  (add_tag eq (subst_cmatch eq tm1), tm2, n-1)

(* slow: consider putting the tagged term in the board *)
fun available_movel (tm,_,_) = 
  filter (fn eq => can (subst_cmatch eq) tm) movel

fun status_of (board as (tm1,tm2,n)) =
  if term_eq tm1 tm2 then Win
  else if n <= 0 orelse cterm_size tm1 > tmsize_limit then Lose 
  else Undecided

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
  move_compare = Term.compare,
  movel = movel
  }

(* -------------------------------------------------------------------------
   Test of MCTS and big steps
   ------------------------------------------------------------------------- *)

fun mk_mctsparam nsim =
  {
  nsim = nsim, stopatwin_flag = true,
  decay = 1.0, explo_coeff = 2.0,
  noise_coeff = 0.25, noise_root = false,
  noise_all = false, noise_gen = random_real,
  noconfl = false, avoidlose = false
  }

fun string_of_status status = case status of
    Win => "win"
  | Lose => "lose"
  | Undecided => "undecided"

fun mcts_test nsim board =
  let
    val mcts_obj =
      {mctsparam = mk_mctsparam nsim,
       game = game,
       player = uniform_player game}
    val tree = starttree_of mcts_obj board
    val (endtree,_) = mcts mcts_obj tree
    val b = #status (dfind [] endtree) = Win
  in
    print_endline (string_of_status (#status (dfind [] endtree)));
    (b, endtree)
  end

val bsobj : (board,move) psBigSteps.bsobj =
  {
  verbose = true,
  temp_flag = false,
  player = psMCTS.random_player game,
  game = game,
  mctsparam = mk_mctsparam 1600
  };

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "mleLib"; open mleLib;
load "mleRewrite"; open mleRewrite;
val board = (tag (random_cterm 20),cT,40);
val _ = (print_endline o cts o #1) board;
val ((b,endtree),t) = add_time (mcts_test 1600) board;
let val nodel = trace_win (#status_of game) endtree [] in
  app (print_endline o cts o #1 o #board) nodel
end;
val _ = psBigSteps.run_bigsteps bsobj board;
print_endline (bts b);
*)

(*
val cj = mk_eq (#1 board,#2 board);
val goal = ([s_thm',k_thm'],cj);
val (gr,_) = METIS_TAC [] goal;
val board = valOf (random_board_try 1000 40 10);
val tm = #1 board;
print_endline (cts tm); 
val tml = strip_cA tm;
app (print_endline o cts) tml;
*)

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let val (l1,l2,l3) = split_triple boardl in
    export_terml (file ^ "_in") l1;
    export_terml (file ^ "_out") l2; 
    writel (file ^ "_timer") (map its l3)
  end

fun read_boardl file =
  let
    val l1 = import_terml (file ^ "_in")
    val l2 = import_terml (file ^ "_out")
    val l3 = map string_to_int (readl (file ^ "_timer"))
  in
    combine_triple (l1,l2,l3)
  end

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

fun lo_walk (n,maxn) tm =
  if cterm_size tm > tmsize_limit then NONE 
  else if is_tagged_nf tm then SOME (tm,n)
  else if n >= maxn then NONE
  else lo_walk (n+1,maxn) (apply_move (hd (available_movel board)) board)
 
fun create_board maxn tm = 
  let val nfo = lo_walk (0,maxn) tm in
    if not (isSome nfo) then NONE else 
    let val (nf,n) = valOf nfo in
      (* if can (find_term (C tmem [cS,cK])) nf 
      then NONE 
      else *) SOME (tm,nf,n)
    end
  end

fun create_boardl n = 
  List.mapPartial (create_board 1000) (gen_exhaustive n)

val datadir = HOLDIR ^ "/src/AI/experiments/data_combin"
val datafile =  datadir ^ "/train-" ^ its version

val stats_dir = HOLDIR ^ "/src/AI/experiments/stats_combin"
fun stats_il header il = 
  let 
    fun f (a,b) = its a ^ "-" ^ its b
    val l = dlist (count_dict (dempty Int.compare) il) 
    val _ = mkDir_err stats_dir
    val s = header ^ "\n" ^ String.concatWith ", " (map f l) ^ "\n"
  in
    append_file (stats_dir ^ "/stats-" ^ its version) s;
    print_endline s
  end

fun export_targetl targetl = 
  (mkDir_err targetdir; write_boardl targetfile targetl)

fun import_targetd () =
  let 
    val l1 = read_boardl targetfile
    val l2 = number_snd 0 l1
    val l3 = map (fn (x,i) => (x,(i,[]))) l2
  in
    dnew board_compare l3
  end

(*
load "aiLib"; open aiLib;
load "psTermGen"; open psTermGen;
load "psMCTS"; open psMCTS;
load "mleRewrite"; open mleRewrite;
val boardl = create_data 4000;
val boardl1 = first_n 400 boardl;
val board = random_elem boardl1;
val rl = map (mcts_test 1600) boardl1;
val rlno = map snd (filter (not o fst) rl);
length rlno;
val nodel = dlist (hd rlno);

val board =(tag (random_cterm 20),T,0);
val ml = (#available_movel (#game rlobj)) board;
val board1 = (#apply_move (#game rlobj)) (hd ml) board;
app (print_endline o cts o #1) [board,board1];
*)

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val head_eval = mk_var ("head_eval", ``:'a -> 'a``)
val head_poli = mk_var ("head_poli", ``:'a -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)
fun tob board = [tag_heval (mk_cE (tm1,tm2)), tag_hpoli (mk_cE (tm1,tm2))]

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 40}]
val dim = 8
fun dim_head_poli n = [dim,n]
val tnnparam = map_assoc (dim_std (1,dim)) [cE,cT,cA,cS,cK] @ 
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]
val dplayer = {tob = tob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleRewrite-combin-" ^ its version, exwindow = 40000,
   ncore = 32, level_threshold = 0.9, nsim = 1600, decay = 0.95}

val rlobj : (board,move) rlobj =
  {
  rlparam = rlparam,
  game = game,
  gameio = gameio,
  level_targetl = level_targetl,
  dplayer = dplayer
  }

val extsearch = mk_extsearch "mleRewrite.extsearch" rlobj

(*
load "mlReinforce"; open mlReinforce;
load "mleRewrite"; open mleRewrite;
val _ = create_data 4000;
val r = rl_start (rlobj,extsearch) 10;

todo: avoid duplicate boards + 
make different paths from the same starting point.
*)

(* -------------------------------------------------------------------------
   Training test
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psTermGen"; open psTermGen;
load "mleRewrite"; open mleRewrite;
val {available_movel, apply_move, ...} = #game rlobj;

fun gen_ex sizeo (n1,n2) =
  let
    val size = if isSome sizeo then valOf sizeo else random_int (n1,n2)
    val tm = elim_kred (random_term [cA,cS,cK] (2*size-1,alpha)); 
    val board = (tm,F,0);
    val movel = available_movel board;
    val tot = length movel
  in
    if tot <> 2 then gen_ex (SOMEval (b,_,_) = psBigSteps.run_bigsteps bsobj board; size) (n1,n2) else
    let
      val moven = random_int (0, tot - 1);
      val move = List.nth (movel,moven);
      val expectv = List.tabulate (tot, fn x => if x = moven then 1.0 else 0.0)
      val (newtm,_,_) = apply_move move board
      val (tm',newtm') = (subst ccsubst tm, subst ccsubst newtm)
    in
      [(tag_hpoli tot (mk_cE (tm,newtm)),expectv)]
    end
  end;

val exl = List.tabulate (10000, fn _ => gen_ex NONE (15,15));

val tml = map fst (List.concat exl);
val d = dregroup Int.compare (map swap (map_assoc term_size tml));
val l = map_snd length (dlist d);

load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val {schedule,tnnparam,tob} = #dplayer rlobj;
val (exl1,exl2) = part_pct 0.9 exl
val tnn = train_tnn schedule (random_tnn tnnparam) (exl1,exl2);
val (pos,neg) = partition (is_accurate tnn) exl2;
val acc = tnn_accuracy tnn exl2;

0.975
val r = hd neg; cts (fst (hd r));

val size = 50;
val tm1 = random_term [cA,cS,cK] (2*size-1,alpha);
val (b,_,_) = psBigSteps.run_bigsteps bsobj board;


val tm2 = elim_kred tm1;
val tm3 = tag_all_redex tm2;
app (print_endline o cts) [tm1,tm2];

measure of complexity: 
  1) how many tries it takes the random strategy to solve it?
  2) does the left-outermost rewriting on both sides solve it?
*)


end (* struct *)
