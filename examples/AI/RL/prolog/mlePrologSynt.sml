(* ========================================================================= *)
(* FILE          : mlePrologSynt.sml                                         *)
(* DESCRIPTION   : Prolog program synthesis                                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
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

fun find_mvar po tm =
  if is_comb tm then
    let val (oper,argl) = strip_comb tm in
      tryfind (find_mvar (SOME tm)) argl
    end
  else if is_mvar tm then (po,tm) else raise ERR "find_mvar" ""

fun mk_mvar ty = mk_var ("M",ty)
fun is_svar x = is_var x andalso "M" <> fst (dest_var x)
fun is_xvar x = is_var x andalso String.isPrefix "x" (fst (dest_var x))
fun is_lvar x = is_var x andalso String.isPrefix "l" (fst (dest_var x))
fun nov x = string_to_int (tl_string (fst (dest_var x)))

fun mk_msubst oper =
  let
    val (domtyl,imty) = strip_type (type_of oper)
    val res = list_mk_comb (oper, map mk_mvar domtyl)
  in
    [{redex = mk_mvar imty, residue = res}]
  end

val close_qt_sub =
  [{redex = mk_mvar (type_of listSyntax.nil_tm), residue = listSyntax.nil_tm}]
fun close_qt qt = subst close_qt_sub qt

val open_qt_sub =
  [{redex = listSyntax.nil_tm, residue = mk_mvar (type_of listSyntax.nil_tm)}]
fun open_qt qt = subst open_qt_sub qt

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (term * bool) list * term
fun string_of_board board = tts (#2 board)
fun board_compare ((_,a),(_,b)) = Term.compare (a,b)

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

(*
fun pretest_qt qt =
  let val clausel = strip_cons [] qt in
    all no_singletonvar (filter (not o contain_mvar) clausel)
  end
*)

fun test_ex prog ex = case ex of [] => Win | e :: m =>
  let val (b1,b2) = test_io prog e in
    if (not b1) then Undecided
    else if (not b2) then Lose
    else test_ex prog m
  end
(*
  case ex of [] => if b then status else Lose
  | e :: m =>
  let val (b1,b2) = test_io prog e in
    if b1 then test_ex (true,status) prog m
    else if b2 then test_ex (b,Undecided) prog m
    else Lose
  end
*)

fun status_of (board as (ex,qt)) =
  if is_mvar qt then Undecided else
  let val qt' = close_qt qt in
    (* if term_size qt > 29 then Lose else *)
    if not (contain_mvar qt')
    then Profile.profile "test_ex" (test_ex (qt_to_prog qt')) (shuffle ex)
    else Undecided
  end

(*
load "mlePrologSynt"; open mlePrologSynt;
load "mlePrologLib"; open mlePrologLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;
val ex = all_ex progdel ;
val b = test_ex (false,Win) prog0 ex;
*)


(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term,term) subst

val movel = map mk_msubst (operlsorted @ all_var (2,2))

fun string_of_move m = tts (#residue (hd m))
fun move_compare (m1,m2) = Term.compare (#residue (hd m1),#residue (hd m2))

fun available_movel (_,qt) =
  if is_mvar qt then map mk_msubst [listSyntax.cons_tm] else
  let
    val (po,mvar) = find_mvar NONE qt
    val clause = (hd o strip_cons []) qt
    val (xn,ln) =
      let
        val xl = map nov (find_terms is_xvar clause)
        val xn' = if null xl then 0 else list_imax xl + 1
        val ll = map nov (find_terms is_lvar clause)
        val ln' = if null ll then 0 else list_imax ll + 1
      in
        (Int.min (xn' + 1,2), Int.min (ln' + 1,2))
      end
    val varl =
      let val (head,body) = (rand (rator clause), rand clause) in
        if is_mvar body
        then all_var (2,2)
        else mk_term_set (find_terms is_svar head)
      end
      handle HOL_ERR _ => all_var (2,2)
    val varl_filtered = filter (fn x => tmem x varl) (all_var (xn,ln))

    val operl_filtered =
      let
        val p = (fst o strip_comb o valOf) po
        fun test x = tmem x [numSyntax.suc_tm,cons_bool,cons_num]
                     andalso term_eq x p
      in
        filter (not o test) operlsorted
      end
    val subl = map mk_msubst (operlsorted @ varl_filtered)
  in
    filter (fn x => term_eq (#redex (hd x)) mvar) subl
  end

fun apply_move move (ex,qt) =
  let
    val newboard as (_,newqt) = (ex, subst_occs [[1]] move qt)
    val movel = available_movel newboard
  in
   if length movel <> 1 orelse
      not (contain_mvar (close_qt newqt)) orelse
      status_of newboard <> Undecided
   then newboard
   else apply_move (hd movel) newboard
  end

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

(*
load "mlePrologSynt"; open mlePrologSynt;
load "mlePrologLib"; open mlePrologLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;
load "Profile";

val mctsparam =
  {
  timer = NONE: real option,
  nsim = SOME 1000000 : int option,
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = false,
  avoidlose = true,
  evalwin = false
  };

val mctsobj = {game = game, mctsparam = mctsparam,
  player =  psMCTS.random_player game};

val table = create_table (progleq @ progsorted) cstrsorted;
val startqt = open_qt (prog_to_qt progleq);
  (* mk_var ("M",``:'a list``); *)
val tree = starttree_of mctsobj (table,startqt);

Profile.reset_all ();
val ((a,(newtree,b)),t) = add_time (mcts mctsobj) tree;
Profile.results ();

val terml =
  filter (not o contain_mvar)
    (map (close_qt o snd o #board o snd) (dlist newtree));

fun is_mvar x = is_var x andalso "M" = fst (dest_var x) andalso type_of x <> ``:'a list``;
fun contain_mvar tm = can (find_term is_mvar) tm;
val nodel = filter (fn (id,x) => not (contain_mvar (#2 (#board x))))
  (dlist newtree);


length nodel;
val nodel2 = filter (fn (id,x) => #stati x = Lose) nodel;
length nodel2;
val tml = map (fn (id,x) => (snd o #board) x) nodel2;
val tml2 = filter (fn x => term_size x >= 5 andalso term_size x <= 18 andalso
   term_size ((rand o rand o rator) x) <= 1) tml;


val qt = ``rule (del x0 (x0::l0) l0) [] :: M``;
val nodel3 = filter (fn x => term_eq ((snd o #board o snd) x) qt) (dlist newtree);


val terml = mk_term_set (map (fn (id,x) => (snd o #board) x) nodel);

val nodel = filter (fn (id,x) => #stati x = Lose) (dlist newtree);
val nodewinl = trace_win newtree [];
val terml = map (snd o #board) nodewinl;

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
