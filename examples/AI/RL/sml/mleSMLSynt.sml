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
val selfdir = HOLDIR ^ "/examples/AI/RL/sml"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

fun string_of_board (_,ol,progll) =
  String.concatWith " " (map its ol) ^ "\n" ^ string_of_progll progll

fun board_compare (a,b) = Term.compare (term_of_board a, term_of_board b)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

val movel =
  (map BIns instrl) @ [BTest,BRec] @
  map BProj (List.tabulate (maxvar,I)) @
  map BSub (List.tabulate (maxvar,fn x => x + 1)) @ [BEndSub]

fun string_of_move m = case m of
    BIns (name,_,_) => name
  | BTest => "test"
  | BRec => "rec"
  | BProj i => "proj" ^ its i
  | BSub i => "sub" ^ its i
  | BEndSub => "endsub"

fun move_compare (m1,m2) =
  String.compare (string_of_move m1, string_of_move m2)

fun apply_move move (n,ol,progll) = (n+1,ol, build move progll)

fun available_movel board = filter (available board) movel

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

fun gen_seql_aux nstep n d' d =
  (
  if d' <> dlength d andalso dlength d mod 100 = 0
    then print_endline (its (dlength d)) else ();
  if dlength d >= n then first_n n (dkeys d) else
  let val l = map (fn x => (x,())) (random_seql nstep) in
    gen_seql_aux nstep n (dlength d) (daddl l d)
  end
  )

fun gen_seql nstep n =
  gen_seql_aux nstep n 0 (dempty (list_compare Int.compare))

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

val seql = gen_seql maxstep 5500;
val seql2 = shuffle seql; length seql2;
val (train,test) = part_n 5000 seql2;
val train' = dict_sort (list_compare Int.compare) train
val test' = dict_sort (list_compare Int.compare) test;

writel (selfdir ^ "/target/train10") (map ilts train');
writel (selfdir ^ "/target/test10") (map ilts test');
*)


(* -------------------------------------------------------------------------
   Test MCTS
   ------------------------------------------------------------------------- *)

(*
load "mleSMLSynt"; open mleSMLSynt;
load "aiLib"; open aiLib;
load "psMTCS"; open psMCTS;
load "psBigSteps"; open psBigSteps;
load "mleSMLLib"; open mleSMLLib;


val mctsparam =
  {explo_coeff = 2.0,
   noise = false, noise_coeff = 0.25, noise_gen = random_real,
   nsim = SOME 100000 : int option, time = NONE: real option};

val tnn = mlTreeNeuralNetwork.read_tnn (selfdir ^ "/eval/cache5/tnn105");

val mctsobj = {game = game, mctsparam = mctsparam,
  player =  #player_from_tnn (#dplayer rlobj) tnn};


fun seqf n = if n = 0 then 0 else n + seqf (n-1);
val seq = List.tabulate (16,seqf);
val startprog = [(1,[])];
val startboard = (0,seq,startprog);

aiLib.debug_flag := true;
val (b,_) = run_bigsteps (false, mctsobj) startboard;




*)









(*
val tree = starting_tree mctsobj startboard;
Profile.reset_all ();
val (_,t) = add_time (mcts mctsobj) tree;
Profile.results ();
PolyML.print_depth 10;
tree
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


load "mleSMLSynt"; open mleSMLSynt;
load "mleSMLLib"; open mleSMLLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;
val progll = random_progll 30;
print_endline (string_of_progll progll);
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
   Neural network embbeddings cache
   ------------------------------------------------------------------------- *)

datatype embtree = EmbNode of real vector option * embtree vector | EmbLeaf

val opernd = dnew Term.compare (number_snd 0 operl)
val operl_length = length operl
val embleafv = Vector.tabulate (operl_length, fn _ => EmbLeaf)

fun n_oper oper = dfind oper opernd

fun embtree_find embtree tml = case embtree of
    EmbLeaf => NONE
  | EmbNode (embo,treev) =>
    (case tml of [] => embo | a :: m =>
     let val (oper,argl) = strip_comb a in
       embtree_find (Vector.sub (treev,n_oper oper)) (argl @ m)
     end)

fun embline tml emb = case tml of
    [] => EmbNode (SOME emb, embleafv)
  | a :: m =>
    let val (oper,argl) = strip_comb a in
       EmbNode (NONE, Vector.update
         (embleafv, n_oper oper, embline (argl @ m) emb))
    end

fun embtree_add embtree tml emb = case embtree of
    EmbLeaf => embline tml emb
  | EmbNode (embo,treev) =>
    (case tml of [] => EmbNode (SOME emb,treev) | a :: m =>
     let
       val (oper,argl) = strip_comb a
       val n = n_oper oper
       val tree1 = Vector.sub (treev,n)
       val tree2 = embtree_add tree1 (argl @ m) emb
     in
       EmbNode (embo, Vector.update (treev,n,tree2))
     end)

fun infer_emb_cache (cache,n) tnn tm =
  case embtree_find (!cache) [tm] of SOME emb => emb | NONE =>
  let
    val (oper,argl) = strip_comb tm
    val embl = map (infer_emb_cache (cache,n) tnn) argl
    val emb = fp_emb tnn oper embl
  in
    cache := embtree_add (!cache) [tm] emb; incr n; emb
  end


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


fun player_from_tnn tnn =
  let
    val olemb_mem = ref NONE
    val xcache = ref EmbLeaf
    val ycache = ref 0
  in
    (
    fn board =>
    let
      val olemb = if isSome (!olemb_mem) then valOf (!olemb_mem) else
        let val r = infer_emb tnn (term_of_natl (#2 board)) in
          olemb_mem := SOME r; r
        end
      val _ =
        if !ycache > 200000 then (xcache := EmbLeaf; ycache := 0) else ()
      val progllemb =
        infer_emb_cache (xcache,ycache) tnn (term_of_progll (#3 board))
      val boardemb = fp_emb tnn ol_cat [olemb,progllemb]
      val e = descale_out (fp_emb tnn head_eval [boardemb])
      val p = descale_out (fp_emb tnn head_poli [boardemb])
      val d = dnew move_compare (combine (movel,p))
      fun f x = dfind x d handle NotFound => raise ERR "player_from_tnn" ""
    in
      (singleton_of_list e, map_assoc f (available_movel board))
    end
    )
  end


val dplayer =
  {player_from_tnn = player_from_tnn,
   tob = tob, tnndim = tnndim, schedule = schedule}


(* -------------------------------------------------------------------------
   OEIS
   ------------------------------------------------------------------------- *)

(*
load "mleSMLSynt"; open mleSMLSynt;
load "aiLib"; open aiLib;
val sl = readl (selfdir ^ "/oeis/pos");
fun ilts il = String.concatWith " " (map its il);
fun f s = map string_to_int
  (tl (first_n 17 (String.tokens (fn x => x = #",") s)));
val l1 = mapfilter f sl; (* filter because of overflow *)
val l2 = filter (fn x => length x = 16) l1;
val l3 = mk_fast_set (list_compare Int.compare) l2;
writel (selfdir ^ "/oeis/oeis_target") (map ilts oeis_seql3);
val l3 = readl (selfdir ^ "/oeis/oeis_target");
fun stil s = map string_to_int  (String.tokens Char.isSpace s);
val l4 = map stil l3;
val l5 = mk_fast_set (list_compare Int.compare) (map (first_n 8) l4);
fun test x = length (mk_fast_set Int.compare x) >= 16 andalso
  all (fn y => y < 1024) x;
val l6 = filter test l4;
*)

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expdir = (mkDir_err (selfdir ^ "/eval"); selfdir ^ "/eval/default"),
   exwindow = 200000, ncore = 30, ntarget = 200, nsim = 100000}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer,
   infobs = fn _ => ()}

val extsearch =
  (debug_flag := false; mk_extsearch selfdir "mleSMLSynt.extsearch" rlobj)

(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleSMLLib"; open mleSMLLib;
load "mleSMLSynt"; open mleSMLSynt;

print_endline (#expdir (#rlparam rlobj));
smlOpen.buildheap_options := "--maxheap 3500";
val targetl = import_targetl "train";
val targetd = mk_targetd targetl;
val r = rl_start (rlobj,extsearch) targetd;
*)

(* todo: 
1) training with multiple objectives.
3) redirect objectives
4) consider evaluating partial programs for extra-knowledge.
*)

end (* struct *)
