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

(* -------------------------------------------------------------------------
   Vocabulary
   ------------------------------------------------------------------------- *)

fun new_const (s,ty) = mk_var (s,ty)
val cI = new_const ("cI",alpha);
val cK = new_const ("cK",alpha);
val cS = new_const ("cS",alpha);
val cA = new_const ("cA",``:'a -> 'a -> 'a``);
val cT = new_const ("cT",``:'a -> 'a``);
val vf = mk_var ("vf",alpha);
val vg = mk_var ("vg",alpha);
val vy = mk_var ("vy",alpha);
val vx = mk_var ("vx",alpha);
infix oo;
fun op oo (a,b) = list_mk_comb (cA,[a,b]);
fun tag x = mk_comb (cT,x);

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = term * term * int
val board_compare = triple_compare Term.compare Term.compare Int.compare
fun string_of_board (a,b,c) = tts a ^ " " ^ tts b ^ " " ^ its c

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = string * term

val k_thm = mk_eq (cK oo vx oo vy, vx);
val k_tag = let val (a,b) = dest_eq k_thm in mk_eq (tag a, b) end;
val s_thm = mk_eq (cS oo vf oo vg oo vx, (vf oo vx) oo (vg oo vx));    
val s_tag = let val (a,b) = dest_eq s_thm in mk_eq (tag a, b) end;
val rand_thm = mk_eq (tag (vf oo vg), vf oo tag vg);
val rator_thm = mk_eq (tag (vf oo vg), tag vf oo vg);

val movel = [("k",k_tag),("s",s_tag),("rand",rand_thm),("rator",rator_thm)];

fun is_cconst x = hd_string (fst (dest_var x)) = #"c"

fun is_cmatch eq tm = 
  let val (sub,_) = match_term (lhs eq) tm in
    not (exists is_cconst (map #redex sub))
  end
  handle HOL_ERR _ => false

fun exists_cmatch eq tm = can (find_term (is_cmatch eq)) tm
fun is_rewritable tm = exists (C exists_cmatch tm) [k_thm,s_thm]

fun subst_match eq tm =
  let 
    val subtm = find_term (is_cmatch eq) tm
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst_occs [[1]] sub2 tm
  end

fun contains_tag tm = can (find_term (term_eq cT)) tm

fun string_of_move move = fst move
fun move_compare (m1,m2) = 
  String.compare (string_of_move m1, string_of_move m2)

fun apply_move_once (move : move) (tm1,tm2,n) = 
  let 
    val tm1' = subst_match (snd move) tm1
    val tm1'' = if contains_tag tm1' then tm1' else tag tm1' 
  in
    (tm1'', tm2, n)
  end

fun apply_move_once_count (move : move) (tm1,tm2,n) = 
  let 
    val tm1' = subst_match (snd move) tm1
    val tm1'' = if contains_tag tm1' then tm1' else tag tm1' 
  in
    (tm1'', tm2, n-1)
  end

fun available_move (board as (tm,_,_)) (move as (_,eq)) = 
  if not (can (subst_match eq) tm) then false else
  let val tm' = subst_match eq tm in
    if not (contains_tag tm') then true else
    let val subtm = 
      rand (find_term (fn x => term_eq (fst (dest_comb x)) cT) tm') 
    in
      is_rewritable subtm
    end
  end

fun status_of (board as (tm1,tm2,n)) =
  if term_eq tm1 tm2 then Win
  else 
    if n <= 0 orelse not (is_rewritable tm1) orelse
       null (filter (available_move board) movel) 
    then Lose 
  else Undecided

fun apply_uniq_move board =
  if status_of board <> Undecided then board else
    case filter (available_move board) movel of
      [] => board
    | [a] => apply_uniq_move (apply_move_once a board)
    | _ => board

fun apply_move move board = 
  apply_uniq_move (apply_move_once_count move board)

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
   MCTS test with uniform player
   ------------------------------------------------------------------------- *)

fun mk_mcts_param nsim =
  {
  nsim = nsim, stopatwin_flag = true,
  decay = 1.0, explo_coeff = 2.0,
  noise_coeff = 0.25, noise_root = false,
  noise_all = false, noise_gen = random_real
  }

fun string_of_status status = case status of
    Win => "win"
  | Lose => "lose"
  | Undecided => "undecided"

fun mcts_test nsim board =
  let
    val mcts_obj =
      {mcts_param = mk_mcts_param nsim,
       game = game,
       player = random_player game}
    val tree = starttree_of mcts_obj board
    val endtree = mcts mcts_obj tree
    val b = #status (dfind [] endtree) = Win
  in
    print_endline (string_of_status (#status (dfind [] endtree)));
    (b, endtree)
  end

fun cts_par tm = 
  if is_const tm then tl_string (fst (dest_const tm)) else 
    case (snd (strip_comb tm)) of
      [a] => "[" ^ cts a ^ "]"
    | [a,b] =>  "(" ^ cts a ^ " " ^ cts_par b ^ ")"
    | _ => raise ERR "cts_par" ""
and cts tm = 
  if is_const tm then tl_string (fst (dest_const tm)) else 
    case (snd (strip_comb tm)) of
      [a] => "[" ^ cts a ^ "]"
    | [a,b] =>  cts a ^ " " ^ cts_par b
    | _ => raise ERR "cts" ""

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "psTermGen"; open psTermGen;
load "mleRewrite"; open mleRewrite;
val board = hd (level_targetl 30);
val (b,endtree) = mcts_test 16000 board1;
val nodel = trace_win (#status_of game) endtree [];
todo: cite machine learning and combinators paper statistics.
*)

(* -------------------------------------------------------------------------
   Level
   ------------------------------------------------------------------------- *)

fun random_walk n board =
  if n <= 0 then board else
  let val movel' = filter (available_move board) movel in
    if null movel' then board else
    random_walk (n-1) (apply_move (random_elem movel') board)
  end

fun random_cterm n = random_term [cA,cS,cK] (n,alpha);
fun random_board size nstep =
  let 
    val tm = tag (random_cterm (2 * size - 1))
    val board1 = (tm, mk_var("none",alpha), nstep + 1)
    val board2 = random_walk nstep board1
  in
    (tm, #1 board2, 2 * (nstep + 1 - (#3 board2))) 
  end

fun level_target level =
  let 
    val size = random_int (5, level) 
    val nstep = random_int (1, level)
  in
    apply_uniq_move (random_board size nstep)
  end  

fun level_targetl level = List.tabulate (400, fn _ => level_target level)

(*
load "aiLib"; open aiLib;
load "mleRewrite"; open mleRewrite;
load "psTermGen"; open psTermGen;
val [(tm1,tm2,n)] = level_targetl 20 1;
print_endline (cts tm1); 
print_endline (cts tm2);
print_endline (its n);
*)

(* -------------------------------------------------------------------------
   Neural representation of the board
   ------------------------------------------------------------------------- *)

val cE = mk_var ("cE", ``:'a -> 'a -> 'a``)
fun term_of_board (tm1,tm2,n) = list_mk_comb (cE,[tm1,tm2])
val operl = map_assoc arity_of [cE,cA,cT,cS,cK]

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let val (l1,l2,l3) = split_triple boardl in
    export_terml (file ^ "_in") l1;
    export_terml (file ^ "_out") l2; 
    writel (file ^ "_max") (map its l3)
  end
fun read_boardl file =
  let
    val l1 = import_terml (file ^ "_in")
    val l2 = import_terml (file ^ "_out")
    val l3 = map string_to_int (readl (file ^ "_max"))
  in
    combine_triple (l1,l2,l3)
  end

val pre_extsearch = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Players
   ------------------------------------------------------------------------- *)

val schedule_base =
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]

val dhtnn_param_base =
  {
  operl = operl, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 8, dimpoli = length movel
  }

val player_base =
  {playerid = "base",
   dhtnn_param = dhtnn_param_base, schedule = schedule_base}

fun term_of_boardc (_:unit) b = term_of_board b

val pretobdict = dnew String.compare
  [("base", (term_of_board, term_of_boardc))]

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rl_param =
  {expname = "mleRewrite-combin-1", ex_window = 80000,
   ncore_search = 4, nsim = 160, decay = 1.0}

val rlpreobj : (board,move,unit) rlpreobj =
  {
  rl_param = rl_param,
  max_bigsteps = (fn (_,_,n) => 10000),
  game = game,
  pre_extsearch = pre_extsearch,
  pretobdict = pretobdict,
  precomp_dhtnn = (fn _ => (fn _ => ())),
  dplayerl = [player_base],
  level_targetl = level_targetl
  }

val extsearch = mk_extsearch "mleRewrite.extsearch" rlpreobj
val rlobj = mk_rlobj rlpreobj extsearch

(*
load "mlReinforce"; open mlReinforce;
load "mleRewrite"; open mleRewrite;


val exl = #read_exl rlobj 
  (HOLDIR ^ "/src/AI/experiments/eval/mleRewrite-combin-1/ex0");
fun term_of_board (tm1,tm2,n) = list_mk_comb (cE,[tm1,tm2])
val dhex = map (fn (a,b,c) => (term_of_board a,b,c)) exl;

load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val dhtnn = train_dhtnn schedule_base (random_dhtnn dhtnn_param_base) dhex;

val r = rl_start_sync rlobj 6;
*)

end (* struct *)
