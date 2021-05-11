(* ========================================================================= *)
(* FILE          : mleSMLSynt.sml                                            *)
(* DESCRIPTION   : SML program synthesis                                     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
(* ========================================================================= *)

structure mleSMLSynt :> mleSMLSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData mleSMLLib

val ERR = mk_HOL_ERR "mleSMLSynt"
val selfdir = HOLDIR ^ "/examples/AI_tasks/sml_synthesis"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = int list * (int * prog list) list
fun string_of_board board = "board" (* todo *)
fun board_compare (p1,p2) = EQUAL (* todo *)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = bprog

val maxvar = 1
val movel =
  (map BIns instrl) @ [BTest,BRec] @ 
  map BProj (List.tabulate (maxvar,I)) @
  map BStartSub (List.tabulate (maxvar,fn x => x + 1)) @ [BEndSub]

fun string_of_move m = "move" (* todo *)
fun move_compare (m1,m2) = EQUAL (* todo *)
  
fun apply_move m (a : int list,b) = (a,build m b)

fun available_movel board =
  let fun test x =
    (ignore (apply_move x board); true) handle Unbuildable => false
  in
   filter test movel
  end

fun timelimit i = (i+1) * (i+1) * (i+1) * 20

fun compare_ol_aux i ol prog = case ol of
    [] => Win
  | a :: m => 
    let val r = exec (timelimit i) prog [i] in
      if isSome r andalso valOf r = a 
      then compare_ol_aux (i+1) m prog
      else Undecided
    end

fun compare_ol ol prog = compare_ol_aux 0 ol prog

fun status_of (ol,progll) = case progll of 
   [(arity : int,[prog])] => compare_ol ol prog
  | _ => Undecided

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
      (_, [(_,[prog])]) => 
      let 
        val r = compute_ol seqlength prog 
        val newseql = (if isSome r then valOf r :: seql else seql)
      in
        random_seql_aux (n-1) newseql newboard
      end
    | _ => random_seql_aux (n-1) seql newboard
  end

val fakeboard = ([],[(1,[])]);

fun random_seql nstep = random_seql_aux nstep [] fakeboard

fun gen_seql_aux nstep n d = 
  if dlength d >= n then first_n n (dkeys d) else
  let val l = map (fn x => (x,())) (random_seql nstep) in
    gen_seql_aux nstep n (daddl l d)
  end

fun gen_seql nstep n = 
  gen_seql_aux nstep n (dempty (list_compare Int.compare))


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
val seql = gen_seql 30 2200;
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

local open SharingTables HOLsexp;

fun enc_prog prog = case prog of
    Ins ((name,_,_),pl) => enc_ins (name,pl)
  | Test (p1,p2,p3) => enc_ins ("test", [p1,p2,p3])
  | Rec pl => enc_ins ("rec",pl)
  | Proj i => enc_ins (its i, [])
  | Sub (p,pl) => enc_ins ("sub",p :: pl)
and enc_ins x = pair_encode (String, list_encode enc_prog) x;

val enc_ol = list_encode Integer;
val enc_state = list_encode (pair_encode (Integer, list_encode enc_prog));
val enc_board = pair_encode (enc_ol, enc_state);

datatype rawprog = Raw of string * rawprog list;

fun dec_prog_raw t = 
  Option.map Raw (pair_decode (string_decode, list_decode dec_prog_raw) t);

fun dec_prog_aux (Raw (s,pl)) = 
  let val pl' = map dec_prog_aux pl in
    if s = "test" then Test (triple_of_list pl')
    else if s = "rec" then Rec pl'
    else if s = "sub" then Sub (hd pl', tl pl')
    else if dmem s instrd then Ins (dfind s instrd, pl')
    else Proj (string_to_int s)
  end;

fun dec_prog t =
  let val x = dec_prog_raw t in 
    if not (isSome x) then NONE else SOME (dec_prog_aux (valOf x))
  end;
    
val dec_ol = list_decode int_decode; 
val dec_state = list_decode (pair_decode (int_decode, list_decode dec_prog));
val dec_board = pair_decode (dec_ol, dec_state);

end

fun write_boardl file boardl = 
  write_data enc_board (file ^ "_board") boardl

fun read_boardl file = 
  read_data decf (file ^ "_board")

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(*
(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/SML_target"

fun create_targetl l =
  let
    val (train,test) = part_pct (10.0/11.0) (shuffle l)
    val _ = export_data (train,test)
    fun f (headnf,combin) = (V1, headnf, 2 * combin_size combin)
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

val head_eval = mk_var ("head_eval", ``:'a list -> 'a``)
val head_poli = mk_var ("head_poli", ``:'a list -> 'a``)
fun tagged_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)

fun tob1 tm = [tag_heval tm, tag_hpoli tm]

fun pretob boardtnno = case boardtnno of
    NONE => tob1
  | SOME (t,tnn) => tob1

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10}]

val dim = 16
fun dim_head_poli n = [dim,n]
val tnndim = map_assoc (dim_std (1,dim)) (operl @ mvarl) @
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]

val dplayer = {pretob = pretob, tnndim = tnndim, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleSMLSynt", exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer,
   infobs = fn _ => ()}

val extsearch = mk_extsearch "mleSMLSynt.extsearch" rlobj
*)




end (* struct *)
