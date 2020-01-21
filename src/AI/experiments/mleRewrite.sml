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

(* -------------------------------------------------------------------------
   Vocabulary
   ------------------------------------------------------------------------- *)

val cI = mk_var ("cI",alpha)
val cK = mk_var ("cK",alpha)
val cS = mk_var ("cS",alpha)
val cX = mk_var ("cX",alpha)
val cY = mk_var ("cY",alpha)
val cZ = mk_var ("cZ",alpha)
val cA = mk_var ("cA",``:'a -> 'a -> 'a``)
val cT = mk_var ("cT",``:'a -> 'a``)
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

val s_thm = mk_eq (tag (cS oo vf oo vg oo vx), (vf oo vx) oo (vg oo vx))
val k_thm = mk_eq (tag (cK oo vx oo vy), vx)
val left_thm = mk_eq (tag (vf oo vg), tag vf oo vg)
val right_thm = mk_eq (tag (vf oo vg), vf oo tag vg)

  
fun strip_cA_aux tm =
  if is_var tm then [tm] else
  let 
    val (oper,argl) = strip_comb tm
    val _ = if term_eq oper cA then () else raise ERR "strip_cA" ""
    val (a1,a2) = pair_of_list argl    
  in
    a2 :: strip_cA_aux a1
  end

fun strip_cA tm = rev (strip_cA_aux tm)

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
fun is_rewritable tm = exists_cmatch s_thm tm
fun is_nf tm = not (is_rewritable tm)

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

fun tag_subtml (tm,posl) =
  if null posl then tm else
  let 
    val (oper,argl) = strip_comb tm 
    fun f i arg = 
      let val posl' = 
        filter (fn pos => not (null pos) andalso hd pos = i) posl
      in
        tag_subtml (arg, map tl posl')
      end
  in
    (if exists null posl then tag else I)
    (list_mk_comb (oper, mapi f argl))
  end

fun tag_eq eq = let val (a,b) = dest_eq eq in mk_eq (tag a, b) end

fun elim_kred tm =
  if can (subst_cmatch k_thm) tm then
    let val tm' = subst_cmatch k_thm tm in
      elim_kred tm'
    end
  else tm

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = term * term * int

fun string_of_board (a,b,c) = cts a ^ "\n" ^ cts b ^ "\n" ^ its c

fun board_compare ((a,b,_),(c,d,_)) = 
  cpl_compare Term.compare Term.compare ((a,b),(c,d))

fun is_combin x = tmem x [cK,cS] 
fun cterm_size tm = length (find_terms is_combin tm) 

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term
val movel = [s_thm,k_thm,left_thm,right_thm]

fun string_of_move eq = tts eq

fun add_tag eq tm =
  if tmem eq [k_thm,s_thm] then tag tm else tm

fun apply_move eq (tm1,tm2,n) = 
  (add_tag eq (subst_cmatch eq tm1), tm2, n-1)

(* very slow: consider putting the tagged term in the board *)
fun available_movel (tm,_,_) = 
  filter (fn eq => can (subst_cmatch eq) tm) movel

fun status_of (board as (tm1,tm2,n)) =
  if term_eq tm1 tm2 then Win
  else if n <= 0 orelse 
    null (available_movel board) orelse 
    cterm_size tm1 > tmsize_limit  
  then Lose 
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

val board = random_cterm 20;

val (board,compl) = valOf (random_board_fixed ());
val _ = ((print_endline o cts o #1) board; (print_endline o cts o #2) board);
val ((b,endtree),t) = add_time (mcts_test 1600) board;
let val nodel = trace_win (#status_of game) endtree [] in
  app (print_endline o cts o #1 o #board) nodel
end;

val rl = map (psBigSteps.run_bigsteps bsobj) (map fst boardl3);
val (rlwin,rllose) = partition #1 rl;
length rlwin;
app (print_endline o cts o #1 o #board) (#3 (hd rlwin));

val board = (tm1,tm2,n);
val _ = psBigSteps.run_bigsteps bsobj board;
print_endline (bts b);

val cj = mk_eq (#1 board,#2 board);
val s_thm' = list_mk_forall ([vf,vg,vx],s_thm);
val k_thm'  = list_mk_forall ([vx,vy],k_thm);
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
   Level
   ------------------------------------------------------------------------- *)

fun random_walk n board =
  if cterm_size (#1 board) > tmsize_limit then NONE else
  if n <= 0 then SOME board else
  let val movel = available_movel board in
    if null movel then NONE else
    random_walk (n-1) (apply_move (random_elem movel) board)
  end

fun lo_norm n tm =
  let 
    val board = (tm,F,0)
    val movel = available_movel board 
  in
    if null movel then SOME tm 
    else if n <= 0 then NONE 
    else lo_norm (n-1) (#1 (apply_move (hd movel) board))
  end
fun is_normalizable tm = isSome (lo_norm 100 tm)

fun random_cterm n = random_term [cA,cS,cK] (2*n-1,alpha);

fun random_board size nstep =
  let 
    val tm = tag (random_cterm size)
    val board1 = (tm, mk_var("dummy",alpha),0)
    val board2 = random_walk nstep board1
  in
    if isSome board2 
    then SOME (tm, #1 (valOf board2), 2*nstep)
    else NONE
  end

fun random_board_try k size nstep =
  let
    fun loop n =
      if n <= 0 then NONE
      else case random_board size nstep of
        NONE => loop (n-1)
      | SOME board => SOME board
  in
    loop k
  end

fun gen_data n =
  if n <= 0 then [] else
  let val boardo = random_board_try 100 20 (random_int (1,10)) in
    if isSome boardo
    then (print_endline (its n); valOf boardo :: gen_data (n-1))
    else gen_data n
  end

val datadir = HOLDIR ^ "/src/AI/experiments/data_combin"
val datafile =  datadir ^ "/train-11"
fun compare_third cmp ((_,_,a),(_,_,b)) = cmp (a,b)

fun stats_il il = 
  let 
    fun f (a,b) = its a ^ "-" ^ its b
    val l = dlist (count_dict (dempty Int.compare) il) 
  in
    print_endline (String.concatWith ", " (map f l))
  end

fun create_data n = 
  let 
    val _ = mkDir_err datadir 
    val l1 = gen_data n
    val l2 = dict_sort (compare_third Int.compare) l1
  in  
    write_boardl datafile l2;
    print_endline "cterm size in:"; 
    stats_il (map (cterm_size o #1) l2);
    print_endline "cterm size out:";
    stats_il (map (cterm_size o #2) l2);
    print_endline "nstep:";
    stats_il (map ((fn x => x div 2) o #3) l2);
    l2
  end

fun div_equal n m = 
  let val (q,r) = (n div m, n mod m) in
    List.tabulate (m, fn i => q + (if i < r then 1 else 0))
  end

fun insert_elem (l,i) a =
  let val (l1,l2) = part_n i l in l1 @ [a] @ l2 end
    
fun shift_elem (i1,i2) l =
  let val (l1,l2) = part_n i1 l in
    if null l2 then l2 else insert_elem (l1 @ tl l2, i2) (hd l2)
  end

fun level_targetl level = 
  let
    val n = 400
    val boardl1 = read_boardl datafile
    val boardl2 = first_n level (mk_batch n boardl1)
    val nl = div_equal n (length boardl2)
  in
    rev (List.concat (map (uncurry random_subset) (combine (nl,boardl2))))
  end

(*
load "aiLib"; open aiLib;
load "psTermGen"; open psTermGen;
load "psMCTS"; open psMCTS;
load "mleRewrite"; open mleRewrite;
val board =(tag (random_cterm 20),T,0);
val ml = (#available_movel (#game rlobj)) board;
val board1 = (#apply_move (#game rlobj)) (hd ml) board;
app (print_endline o cts o #1) [board,board1];
*)

(* -------------------------------------------------------------------------
   Neural representation of the board
   ------------------------------------------------------------------------- *)

fun term_of_board (tm1,tm2,_) = mk_cE (tm1,tm2)

fun tob board =
  let 
    val n = length (available_movel board) 
    val tm = term_of_board board 
  in
    [tag_heval tm, tag_hpoli tm]
  end

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 40}]

val operl = [cE,cT,cA,cS,cK];

val dim = 12
fun dim_head_poli n = [dim,n]

val tnnparam = map_assoc (dim_std (1,dim)) operl @ 
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,dim])]

val dplayer = {tob = tob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleRewrite-combin-11", exwindow = 40000,
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
val _ = create_data 4000;
val r = rl_start (rlobj,extsearch) 1;
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
