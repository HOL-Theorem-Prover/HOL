(* ========================================================================= *)
(* FILE          : mleSMLSynt.sml                                            *)
(* DESCRIPTION   : SML program synthesis                                     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
(* ========================================================================= *)

structure mleSMLSynt :> mleSMLSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS
  mlNeuralNetwork mlTreeNeuralNetwork mlReinforce mlTacticData mleSMLLib

val ERR = mk_HOL_ERR "mleSMLSynt"
val selfdir = HOLDIR ^ "/examples/AI_tasks/sml_synthesis"

type board = int * int list * (int * prog list) list
val maxvar = 1

(* -------------------------------------------------------------------------
   Program size
   ------------------------------------------------------------------------- *)

fun size_of_prog prog =  case prog of
    Ins ((name,_,_),pl) => 1 + sum_int (map size_of_prog pl)
  | Test (p1,p2,p3) => 1 + sum_int (map size_of_prog [p1,p2,p3])
  | Rec pl => 1 + sum_int (map size_of_prog pl)
  | Proj i => 1
  | Sub (p,pl) => 1 + sum_int (map size_of_prog (p :: pl))

fun size_of_progl progl = sum_int (map size_of_prog progl)
fun size_of_progll progll =  sum_int (map (fn (_,a) => size_of_progl a) progll)

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val embed_flag = ref false

(* target *)
val natbase = 16

val nat_cat = mk_var ("nat_cat", rpt_fun_type 3 alpha)
val seq_cat = mk_var ("seq_cat", rpt_fun_type 3 alpha)
fun mk_nat i = mk_var ("nat" ^ its i,alpha)
val natl = List.tabulate (16,mk_nat)

fun term_of_nat n = 
  if n < 0 then raise ERR "term_of_nat" ""
  else if n < natbase then mk_nat n 
  else list_mk_comb (nat_cat, 
    [mk_nat (n mod natbase), term_of_nat (n div natbase)]);

fun term_of_natl nl = 
  if !embed_flag then mk_var ("seqembed",alpha) else
  case nl of
    [] => raise ERR "term_of_natl" ""
  | [a] => term_of_nat a
  | a :: m => list_mk_comb (seq_cat, [term_of_nat a, term_of_natl m]);

(* state *)
fun mk_proj i = mk_var ("proj" ^ its i,alpha)

fun term_of_prog prog = 
  if !embed_flag then mk_var ("progembed",alpha) else
  case prog of
    Ins ((name,_,_),pl) => term_of_namepl (name,pl)
  | Test (p1,p2,p3) => term_of_namepl ("test",[p1,p2,p3])
  | Rec pl => term_of_namepl ("rec" ^ its (length pl),pl)
  | Proj i => mk_proj i
  | Sub (p,pl) => term_of_namepl ("sub" ^ its (length pl), p :: pl)
and term_of_namepl (name,pl) =
  let val v = mk_var (name,rpt_fun_type (length pl + 1) alpha) in
    list_mk_comb (v, map term_of_prog pl)
  end 

val prog_cat = mk_var ("prog_cat", rpt_fun_type 3 alpha)
val progl_cat = mk_var ("progl_cat", rpt_fun_type 3 alpha)
val arity_cat = mk_var ("arity_cat", rpt_fun_type 3 alpha)

fun term_of_progl progl = case progl of
    [] => mk_var ("empty_prog",alpha)
  | [a] => term_of_prog a
  | a :: m => list_mk_comb (prog_cat,[term_of_prog a,term_of_progl m])

fun mk_arity i = mk_var ("arity" ^ its i,alpha)
fun term_of_progll progll = case progll of
    [] => raise ERR "term_of_progll" ""
  | [(a,progl)] => list_mk_comb (arity_cat, [mk_arity a, term_of_progl progl])
  | (a,progl) :: m => list_mk_comb (progl_cat,
    [list_mk_comb (arity_cat, [mk_arity a, term_of_progl progl]),
     term_of_progll m])

(* board *)

val head_eval = mk_var ("head_eval", rpt_fun_type 2 alpha)
val head_poli = mk_var ("head_poli", rpt_fun_type 2 alpha)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)

val ol_cat = mk_var ("ol_cat", rpt_fun_type 3 alpha)

fun term_of_board (_,ol,progll) = 
  let val tm = 
    list_mk_comb (ol_cat, [term_of_natl ol, term_of_progll progll]) 
  in
    [tag_heval tm, tag_hpoli tm]
  end

(* operators *)
val operl = 
  List.tabulate (natbase,mk_nat) @ [nat_cat,seq_cat] @
  List.tabulate (maxvar,mk_proj) @
  [mk_var ("test",rpt_fun_type 4 alpha)] @
  List.tabulate (maxvar + 1, 
     fn i => mk_var ("rec" ^ its i, rpt_fun_type (i+1) alpha)) @
  List.tabulate (maxvar + 1, 
     fn i => mk_var ("sub" ^ its i, rpt_fun_type (i+2) alpha)) @
  map (fn (name,i,_) => mk_var (name, rpt_fun_type (i+1) alpha)) instrl @
  [mk_var ("empty_prog",alpha), prog_cat, progl_cat, arity_cat] @
  List.tabulate (maxvar + 1, mk_arity) @
  [ol_cat]


(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

fun string_of_board board = tts (hd (term_of_board board))
fun board_compare (a,b) = 
  Term.compare (hd (term_of_board a), hd (term_of_board b))

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = bprog

val movel =
  (map BIns instrl) @ [BTest,BRec] @ 
  map BProj (List.tabulate (maxvar,I)) @
  map BStartSub (List.tabulate (maxvar,fn x => x + 1)) @ [BEndSub]

fun string_of_move m = case m of
    BIns (name,_,_) => name
  | BTest => "test"
  | BRec => "rec"
  | BProj i => "proj" ^ its i 
  | BStartSub i => "startsub" ^ its i
  | BEndSub => "endsub"
  
fun move_compare (m1,m2) = 
  String.compare (string_of_move m1, string_of_move m2)
  
fun apply_move m (n, a : int list,b) = (n+1, a, build m b)

fun available_movel board =
  let fun test x =
    (ignore (apply_move x board); true) handle Unbuildable => false
  in
   filter test movel
  end

val maxstep = 30

fun timelimit i = (i+1) * (i+1) * (i+1) * maxstep


fun compare_ol_aux i n ol prog = case ol of
    [] => Win
  | a :: m => 
    let val r = exec (timelimit i) prog [i] in
      if isSome r andalso valOf r = a 
      then compare_ol_aux (i+1) n m prog
      else if n > maxstep then Lose else Undecided
    end

fun compare_ol n ol prog = compare_ol_aux 0 n ol prog

fun status_of (n,ol,progll) = case progll of 
   [(arity : int,[prog])] => compare_ol n ol prog
  | _ => if n > maxstep then Lose else Undecided

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  available_movel = available_movel,
  apply_move = apply_move,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movel
  }

(* -------------------------------------------------------------------------
   Generating random programs and keeping their sequence.
   ------------------------------------------------------------------------- *)

fun compute_ol_aux (i,ibound) seq prog = 
  if i >= ibound then SOME (rev seq) else
  let val r = exec (timelimit i) prog [i] in
     if isSome r 
     then compute_ol_aux (i+1, ibound) (valOf r :: seq) prog
     else NONE
   end

fun compute_ol ibound prog = compute_ol_aux (0,ibound) [] prog

val seqlength = 16

fun random_seql_aux n seql board = 
  if n <= 0 then seql else
  let 
    val movel = available_movel board 
    val newboard = apply_move (random_elem movel) board
  in
    case newboard of
      (_ , _, [(_,[prog])]) => 
      let 
        val r = compute_ol seqlength prog 
        val newseql = (if isSome r then valOf r :: seql else seql)
      in
        random_seql_aux (n-1) newseql newboard
      end
    | _ => random_seql_aux (n-1) seql newboard
  end

val fakeboard = (0,[],[(1,[])])

fun random_seql nstep = random_seql_aux nstep [] fakeboard

fun gen_seql_aux nstep n d = 
  if dlength d >= n then first_n n (dkeys d) else
  let val l = map (fn x => (x,())) (random_seql nstep) in
    gen_seql_aux nstep n (daddl l d)
  end

fun gen_seql nstep n = 
  gen_seql_aux nstep n (dempty (list_compare Int.compare))

(* -------------------------------------------------------------------------
   Generating a random board of a certain size
   ------------------------------------------------------------------------- *)

fun random_progll_aux n board = 
  if n <= 0 then #3 board else
  let 
    val movel = available_movel board 
    val newboard = apply_move (random_elem movel) board
  in
    random_progll_aux (n-1) newboard
  end

fun random_progll nstep = random_progll_aux nstep fakeboard

(* -------------------------------------------------------------------------
   Export test and train set
   ------------------------------------------------------------------------- *)

(*
load "mleSMLSynt"; open mleSMLSynt;
load "mleSMLLib"; open mleSMLLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;
fun ilts il = String.concatWith " " (map its il);
val selfdir = HOLDIR ^ "/examples/AI_tasks/sml_synthesis";
writel (selfdir ^ "/data/train") (map ilts train');
writel (selfdir ^ "/data/test") (map ilts test');
val seql = gen_seql maxstep 2200;
val seqlb = filter (fn x => hd x = 0 andalso hd (tl x) = 0) seql; length seqlb;
val seql2 = shuffle seql; length seql2;
val (train,test) = part_n 2000 seql2;
val train' = dict_sort (list_compare Int.compare) train
val test' = dict_sort (list_compare Int.compare) test;
*)

(* -------------------------------------------------------------------------
   Test MCTS
   ------------------------------------------------------------------------- *)

(* 
load "mleSMLSynt"; open mleSMLSynt;
load "mleSMLLib"; open mleSMLLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;
load "Profile";

val mctsparam =
  {explo_coeff = 2.0,
   noise = false, noise_coeff = 0.25, noise_gen = random_real,
   nsim = SOME 1000000 : int option, time = NONE: real option};
val mctsobj = {game = game, mctsparam = mctsparam,
  player =  psMCTS.uniform_player game};

val seq = [0,1,3,6,10,15,21,28];
val startprog = [(1,[])];
val startboard = (seq, startprog);
val tree = starting_tree mctsobj startboard;
Profile.reset_all ();
val (_,t) = add_time (mcts mctsobj) tree;
Profile.results ();
PolyML.print_depth 10;
tree;

if n = 0 then 0 else n + (f (n-1))
(* 6 characters *)
#status_of game board2;

val movel = #available_movel game startboard;
val board1 = #apply_move game (BProj 0) startboard;
val movel = #available_movel game board1;
val board2 = #apply_move game (List.nth (movel,1)) board1;
val movel = #available_movel game board2;
val board3 = #apply_move game (List.nth (movel,2)) board2;
val movel = #available_movel game board3;
val board4 = #apply_move game (List.nth (movel,3)) board3;
val movel = #available_movel game board4;
val board5 = #apply_move game (List.nth (movel,2)) board4;
val movel = #available_movel game board5;
val board6 = #apply_move game (List.nth (movel,0)) board5;
val movel = #available_movel game board6;
val board7 = #apply_move game (List.nth (movel,4)) board6;
val movel = #available_movel game board7;
val board8 = #apply_move game (List.nth (movel,3)) board7;
*)

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

local open SharingTables HOLsexp in

fun enc_prog prog = case prog of
    Ins ((name,_,_),pl) => enc_ins (name,pl)
  | Test (p1,p2,p3) => enc_ins ("test", [p1,p2,p3])
  | Rec pl => enc_ins ("rec",pl)
  | Proj i => enc_ins (its i, [])
  | Sub (p,pl) => enc_ins ("sub",p :: pl)
and enc_ins x = pair_encode (String, list_encode enc_prog) x

val enc_ol = list_encode Integer
val enc_state = list_encode (pair_encode (Integer, list_encode enc_prog))
val enc_board = pair3_encode (Integer, enc_ol, enc_state)
val enc_boardl = list_encode enc_board

datatype rawprog = Raw of string * rawprog list

fun dec_prog_raw t = 
  Option.map Raw (pair_decode (string_decode, list_decode dec_prog_raw) t)

fun dec_prog_aux (Raw (s,pl)) = 
  let val pl' = map dec_prog_aux pl in
    if s = "test" then Test (triple_of_list pl')
    else if s = "rec" then Rec pl'
    else if s = "sub" then Sub (hd pl', tl pl')
    else if dmem s instrd then Ins (dfind s instrd, pl')
    else Proj (string_to_int s)
  end

fun dec_prog t =
  let val x = dec_prog_raw t in 
    if not (isSome x) then NONE else SOME (dec_prog_aux (valOf x))
  end
    
val dec_ol = list_decode int_decode
val dec_state = list_decode (pair_decode (int_decode, list_decode dec_prog))
val dec_board = pair3_decode (int_decode, dec_ol, dec_state)
val dec_boardl = list_decode dec_board

end (* local *)


fun write_boardl file boardl = write_data enc_boardl file boardl
fun read_boardl file = read_data dec_boardl file
val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* 
load "mleSMLSynt"; open mleSMLSynt;
load "mleSMLLib"; open mleSMLLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;

val ol = [1,2,15,1532,23];
val progll = random_progll 20;
val board = (0,ol,progll);
val board = mk_startboard ol;
#write_boardl gameio "test" [board];
val newboard = #read_boardl gameio "test";
val terml = term_of_board (hd newboard);
*)

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/target"

val startstate = [(1,[])]
fun mk_startboard target = (0,target,startstate) 

fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun import_targetl name = 
  map (mk_startboard o stil) (readl (targetdir ^ "/" ^ name))

fun mk_targetd l = dnew board_compare (map (fn x => (x,[])) l) 


(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10}]

val dim = 16
fun dim_head_poli n = [dim,n]
val tnndim = map_assoc (dim_std (1,dim)) operl @
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]

fun player_from_tnn tnn board =
  let
    val amovel = available_movel board
    (* *)
    val (e,p) = pair_of_list (map snd (infer_tnn tnn (term_of_board board)))
    val d = dnew move_compare (combine (movel,p))
    fun f x = dfind x d handle NotFound => raise ERR "player_from_tnn" ""
  in
    (singleton_of_list e, map_assoc f amovel)
  end

val dplayer = 
  {player_from_tnn = player_from_tnn,
   tob = term_of_board, tnndim = tnndim, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expdir = selfdir ^ "/eval/unoptimized", exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 100000}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer,
   infobs = fn _ => ()}

val extsearch =
  (debug_flag := false; mk_extsearch "mleSMLSynt.extsearch" rlobj)

(* 
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleSMLSynt"; open mleSMLSynt;
load "mleSMLLib"; open mleSMLLib;

val targetl = import_targetl "train";
val targetd = mk_targetd targetl;
val r = rl_start (rlobj,extsearch) targetd;
*)

end (* struct *)
