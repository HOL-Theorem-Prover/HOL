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
val cI = new_const ("cI",alpha)
val cK = new_const ("cK",alpha)
val cS = new_const ("cS",alpha)
val cA = new_const ("cA",``:'a -> 'a -> 'a``)
val cT = new_const ("cT",``:'a -> 'a``)
val cE = mk_var ("cE", ``:'a -> 'a -> 'a``)
val vf = mk_var ("vf",alpha)
val vg = mk_var ("vg",alpha)
val vy = mk_var ("vy",alpha)
val vx = mk_var ("vx",alpha)
val eq_adj = mk_var ("eq_adj", ``:'a -> bool -> 'a``)
val head_eval = mk_var ("head_eval", ``:'a -> 'a``)
val head_poli = mk_var ("head_poli", ``:'a -> 'a``)

fun is_cconst x = is_var x andalso hd_string (fst (dest_var x)) = #"c"

fun mk_cE (a,b) = list_mk_comb (cE,[a,b])
fun tag x = mk_comb (cT,x)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)

infix oo
fun op oo (a,b) = list_mk_comb (cA,[a,b])

val s_thm = mk_eq (cS oo vf oo vg oo vx, (vf oo vx) oo (vg oo vx))
val k_thm = mk_eq (cK oo vx oo vy, vx)

(* -------------------------------------------------------------------------
   Pretty-printing combinator expressions
   ------------------------------------------------------------------------- *)

fun cts_par tm = 
  if is_cconst tm then tl_string (fst (dest_var tm)) else 
    case (snd (strip_comb tm)) of
      [a] => "[" ^ cts a ^ "]"
    | [a,b] =>  "(" ^ cts a ^ " " ^ cts_par b ^ ")"
    | _ => raise ERR "cts_par" ""
and cts tm = 
  if is_cconst tm then tl_string (fst (dest_var tm)) else 
    case (snd (strip_comb tm)) of
      [a] => "[" ^ cts a ^ "]"
    | [a,b] =>  cts a ^ " " ^ cts_par b
    | _ => raise ERR "cts" ""

(* -------------------------------------------------------------------------
   Rewriting
   ------------------------------------------------------------------------- *)

fun is_cmatch eq tm = 
  let val (sub,_) = match_term (lhs eq) tm in
    not (exists is_cconst (map #redex sub))
  end
  handle HOL_ERR _ => false

fun exists_cmatch eq tm = can (find_term (is_cmatch eq)) tm
fun is_rewritable tm = exists (C exists_cmatch tm) [s_thm,k_thm]

fun subst_cmatch eq tm =
  let 
    val subtm = find_term (is_cmatch eq) tm
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst sub2 tm
  end
  handle HOL_ERR _ => raise ERR "subst_cmatch" (cts tm ^ " -- " ^ tts eq)

fun tag_subtm (tm,pos) =
  if null pos then tag tm else
  let 
    val (oper,argl) = strip_comb tm 
    fun f i arg = 
      if i = hd pos then tag_subtm (List.nth (argl,hd pos), tl pos) else arg
  in
    list_mk_comb (oper, mapi f argl)
  end

fun tag_eq eq = let val (a,b) = dest_eq eq in mk_eq (tag a, b) end

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = term * term * int

fun string_of_board (a,b,c) = cts a ^ "\n" ^ cts b ^ "\n" ^ its c

fun board_compare ((a,b,_),(c,d,_)) = 
  cpl_compare Term.compare Term.compare ((a,b),(c,d))

val tmsize_limit = 100
fun is_combin x = tmem x [cK,cS] 
fun cterm_size tm = length (find_terms is_combin tm) 

fun status_of (board as (tm1,tm2,n)) =
  if cterm_size (#1 board) > tmsize_limit then Lose 
  else if term_eq tm1 tm2 then Win
  else if n <= 0 orelse not (is_rewritable tm1) then Lose 
  else Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term * int list

fun string_of_move (eq,pos) = tts eq ^ ", " ^ string_of_pos pos

fun apply_move (eq,pos) (tm1,tm2,n) = 
  (subst_cmatch (tag_eq eq) (tag_subtm (tm1,pos)), tm2, n-1)

fun moveo_poseq tm ((subtm,pos),eq) =
  if is_cmatch eq subtm then SOME (eq,pos) else NONE

fun available_movel (tm,_,_) = 
  let val l = cartesian_product (all_subtmpos tm) ([s_thm,k_thm]) in
    List.mapPartial (moveo_poseq tm) l
  end

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
  board_compare = board_compare
  }

(* -------------------------------------------------------------------------
   MCTS test with uniform player
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
       player = random_player game}
    val tree = starttree_of mcts_obj board
    val (endtree,_) = mcts mcts_obj tree
    val b = #status (dfind [] endtree) = Win
  in
    print_endline (string_of_status (#status (dfind [] endtree)));
    (b, endtree)
  end

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "mleLib"; open mleLib;
load "mleRewrite"; open mleRewrite;
val board = random_board 20 20;
val (_,endtree) = mcts_test 1600 board;
val nodel = trace_win (#status_of game) endtree [];
val step = (length nodel - 1);
val tm1 = #1 (#board (hd nodel)); cts tm1;
*)

(* -------------------------------------------------------------------------
   Level
   ------------------------------------------------------------------------- *)



fun random_walk n board =
  if cterm_size (#1 board) > tmsize_limit then NONE else
  if n <= 0 then SOME board else
  let val movel = available_movel board in
    if null movel then NONE else
    random_walk (n-1) (apply_move (random_elem movel) board)
  end

fun random_cterm n = random_term [cA,cS,cK] (n,alpha);
fun random_board size nstep =
  let 
    val tm = random_cterm (2 * size - 1)
    val board1 = (tm, mk_var("dummy",alpha),0)
    val board2 = random_walk nstep board1
  in
    if isSome board2 
    then SOME (tm, #1 (valOf board2), 2 * nstep) 
    else NONE
  end

fun level_target level =
  let 
    val (a,b) = (random_int (20, level), random_int (1, level))
    fun loop n = 
      if n <= 0 
      then (print_endline ("level_target: " ^ its a ^ " " ^ its b); NONE)
      else case random_board a b of
        NONE => loop (n-1)
      | SOME board => SOME board
  in
    loop 1000
  end

fun level_targetl level = 
  let 
    val l1 = List.tabulate (400, fn _ => level_target level)
    val l2 = map valOf (filter isSome l1)
    fun third_compare cmp ((_,_,a),(_,_,b)) = cmp (b,a)
  in
    dict_sort (third_compare Int.compare) l2
  end    

(*
load "aiLib"; open aiLib;
load "mleRewrite"; open mleRewrite;
val board = random_board 20 5;
val boardl = level_targetl 30;
print_endline (#string_of_board (#game rlobj) board); 
*)

(* -------------------------------------------------------------------------
   Neural representation of the board
   ------------------------------------------------------------------------- *)

fun term_of_board (tm1,tm2,_) = mk_cE (tm1,tm2)

fun term_of_move (tm1,tm2,_) (eq,pos) =
  let val tagboard = mk_cE (tag_subtm (tm1,pos),tm2) in
    list_mk_comb (eq_adj,[tagboard,eq])
  end

fun tob board = 
  tag_heval (term_of_board board) ::
  map (tag_hpoli o term_of_move board) (available_movel board)

val operl = [eq_adj,head_eval,head_poli,``$= :'a->'a->bool``, 
  cE,cT,cA,cS,cK,vx,vy,vf,vg];

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
   Players
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]

val tnnparam = map_assoc (dim_std (2,12)) operl

val dplayer = {tob = tob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleRewrite-combin-2", exwindow = 80000,
   ncore = 32, nsim = 1600, decay = 1.0}

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
val r = rl_start (rlobj,extsearch) 30;
*)

(* -------------------------------------------------------------------------
   Bigsteps test
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleRewrite"; open mleRewrite;
load "psBigSteps"; open psBigSteps;

val game = #game rlobj;

val mctsparam =
  {
  nsim = 1600,
  stopatwin_flag = false,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = true, noise_root = false,
  noise_coeff = 0.25, noise_gen = random_real
  };

val bsobj : (board,move) bsobj =
  {
  verbose = true,
  temp_flag = false,
  player = psMCTS.uniform_player game,
  game = game,
  mctsparam = mctsparam
  };

val board = random_board 40 5;
val _ = run_bigsteps bsobj board;
val (b1,b2,rlex,rootl) = run_bigsteps bsobj board;
*)

(* -------------------------------------------------------------------------
   Training test
   ------------------------------------------------------------------------- *)

(*
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val {schedule,tnnparam,tob} = #dplayer rlobj;
fun f (a,b) = combine (tob a, map (fn x => [x]) b);
val tnnex = map f (List.concat (List.tabulate (16, fn _ => rlex)));
val tnn = train_tnn schedule (random_tnn tnnparam) (tnnex,[]);
*)


end (* struct *)
