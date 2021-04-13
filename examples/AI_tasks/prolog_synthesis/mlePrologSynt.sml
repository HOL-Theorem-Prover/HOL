(* ========================================================================= *)
(* FILE          : mlePrologSynt.sml                                         *)
(* DESCRIPTION   : Specification of term synthesis on combinator datatype    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mlePrologSynt :> mlePrologSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mlePrologLib

val ERR = mk_HOL_ERR "mlePrologSynt"
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Metavar
   ------------------------------------------------------------------------- *)

fun is_mvar x = is_var x andalso "M" = fst (dest_var x)
fun contain_mvar tm = can (find_term is_mvar) tm
fun first_mvar tm = find_term is_mvar tm
fun mk_mvar ty = mk_var ("M",ty)
fun is_svar x = is_var x andalso "M" <> fst (dest_var x)
fun is_xvar x = is_var x andalso String.isPrefix "x" (fst (dest_var x))
fun is_lvar x = is_var x andalso String.isPrefix "l" (fst (dest_var x))

fun nov x = string_to_int (tl_string (fst (dest_var x)))

fun wsize tm = 
  let 
    val (oper,argl) = strip_comb tm
    val n = 
      if is_mvar oper then 
       let val ty = type_of oper in 
         assoc ty [(``:num``,1),(``:num list``,1),(beta,1),(bool,6),
                   (``:bool list``,1),(alpha,8),(``:'a list``,1)]
         handle HOL_ERR _ => raise ERR "wsize" (term_to_string tm)
       end
      else 1
  in
    n + sum_int (map wsize argl)
  end

fun mk_subst oper =
  let 
    val (domtyl,imty) = strip_type (type_of oper) 
    val res = list_mk_comb (oper, map mk_mvar domtyl)
  in
    [{redex = mk_mvar imty, residue = res}]
  end

val anilsubst = mk_subst anil

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (term * term) list * (int * int) * term
fun string_of_board board = tts (#3 board)
fun board_compare ((_,_,a),(_,_,b)) = Term.compare (a,b)

fun no_singletonvar clause = 
  let  
    val vl = find_terms is_var clause
    val vd = count_dict (dempty Term.compare) vl
  in
    all (fn x => x >= 2) (map snd (dlist vd))
  end

fun strip_cons rl qt = 
  let val (a,m) = listSyntax.dest_cons qt in
    strip_cons (a :: rl) m
  end
  handle HOL_ERR _ => rl

fun pretest_qt qt =
  let val clausel = strip_cons [] qt in  
    all no_singletonvar (filter (not o contain_mvar) clausel)
  end

fun test_ex status prog ex = case ex of [] => status | e :: m => 
  let val (b1,b2) = test_unit prog e in
    if b1 then test_ex status prog m 
    else if b2 then test_ex Undecided prog m
    else Lose
  end

fun status_of (board as (ex,_,qt)) =
  if is_mvar qt then Undecided else 
  let val qt' = subst anilsubst qt in
    if wsize qt > 29 orelse not (pretest_qt qt') then Lose else
    if not (contain_mvar qt') 
      then test_ex Win (qt_to_prog qt') ex
      else Undecided
  end

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term,term) subst

val movel = map mk_subst (operl_nn (2,2))

fun string_of_move m = tts (#residue (hd m))
fun move_compare (m1,m2) = Term.compare (#residue (hd m1),#residue (hd m2))
  


fun available_movel (_,(nx,lx),qt) =
  let 
    val mvar = first_mvar qt 
    val operl = operl_nn (nx,lx)
  in
    filter (fn x => term_eq (#redex (hd x)) mvar) (map mk_subst operl)
  end

fun apply_move (tree,id) move (ex,(nx,lx),qt) =
  let 
    val (newnx,newlx) = 
    if type_of (#redex (hd move)) = alpha then (1,1) else 
      if is_xvar (#residue (hd move))
      then (Int.min (2, Int.max (nov (#residue (hd move)) + 2, nx)), lx)
      else 
        if is_lvar (#residue (hd move))
        then (nx, Int.min (2, Int.max (nov (#residue (hd move)) + 2, lx)))
        else (nx,lx)
    val newboard = (ex, (newnx,newlx), subst_occs [[1]] move qt)
    val movel = available_movel newboard
  in
   if length movel <> 1 orelse 
      status_of newboard <> Undecided 
   then (newboard, tree)
   else apply_move (tree,id) (hd movel) newboard
  end


(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = Profile.profile "status_of" status_of,
  available_movel = Profile.profile "available_movel" available_movel,
  apply_move = 
    let fun f x y z = Profile.profile "apply_move" (apply_move x y) z
    in f end
  ,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movel
  }

(* 
load "mlePrologSynt"; open mlePrologSynt;
load "mlePrologLib"; open mlePrologLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;
load "Profile";

val mctsparam =
  {
  timer = NONE: real option,
  nsim = SOME 100000 : int option,
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = false,
  avoidlose = false,
  evalwin = false
  };

val mctsobj = {game = game, mctsparam = mctsparam,
  player =  psMCTS.random_player game};

val ex = all_ex prog0 (2,3);
val startqt = mk_var ("M",``:'a list``);
val tree = starttree_of mctsobj (ex,(1,1),startqt);
val ((a,(newtree,b)),t) = add_time (mcts mctsobj) tree;
Profile.results ();

fun is_mvar x = is_var x andalso "M" = fst (dest_var x) andalso type_of x <> ``:'a list``;
fun contain_mvar tm = can (find_term is_mvar) tm;


val nodel = filter (fn (id,x) => not (contain_mvar (#3 (#board x)))) 
  (dlist newtree);
length nodel;
val nodel2 = filter (fn (id,x) => #stati x = Undecided) nodel;
length nodel2;
val nodel3 = map (#3 o #board o snd) nodel2;


val nodel = filter (fn (id,x) => #stati x = Lose) (dlist newtree);

val nodel = trace_win newtree [];

val nodel = filter (fn (id,x) => 
  contain_mvar (#3 (#board x)) andalso 
  #stati x = Lose) 
  (dlist newtree);

val nodel = filter (fn (id,x) => not (pretest_qt (#3 (#board x))))
  (dlist newtree);


fun is_looping 
  delete (a,b,c) <= delete (a,b,c)
case delete (a,[b,c],y) of
  delete (x1,l1,l2) <= delete (x1,l2,l1)
clause can (no match) (loop)
*)

(*
(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =  export_terml (file ^ "_qt") boardl
fun read_boardl file = import_terml (file ^ "_qt")
val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/prolog_target"

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
fun tag_heval x = mk_comb (head_eval,x)
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
  {expname = "mlePrologSynt", exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer,
   infobs = fn _ => ()}

val extsearch = mk_extsearch "mlePrologSynt.extsearch" rlobj
*)




end (* struct *)
