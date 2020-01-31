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
  mlReinforce mleLib combinTheory

val ERR = mk_HOL_ERR "mleRewrite"

val tmsize_limit = 100
val version = 16

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
val movel = tag_axl_bare
val tag_axl_bare12 = first_n 2 tag_axl_bare
val tag_axl_bare3 = List.nth (tag_axl_bare,2)

fun string_of_move eq = tts eq

fun add_tag eq tm =
  if tmem eq tag_axl_bare12 then mk_tag tm else tm

fun apply_eq eq tm = add_tag eq (subst_match eq tm)
fun apply_move eq (tm1,tm2,n) =
  (add_tag eq (subst_match eq tm1), tm2, n-1)

fun available_eql tm =
  let 
    fun lhs_tag x = fst (dest_cA (dest_tag x))
    fun test eq =
      if term_eq eq tag_axl_bare3
      then 
        can (subst_match eq) tm andalso 
        not (is_nf (lhs_tag (find_term (is_match eq) tm)))
      else can (subst_match eq) tm
  in
    filter test movel 
  end

fun available_movel (tm,_,_) = 
  filter (fn eq => can (subst_match eq) tm) movel

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
  else if is_nf tm then SOME (tm,n)
  else if n >= maxn then NONE
  else 
    let 
      val movel = available_eql tm 
      val _ = print "."
    in
      if null movel 
      then raise ERR "lo_walk" (tts tm)
      else lo_walk (n+1,maxn) (apply_eq (hd movel) tm)
    end

fun create_board maxn (tm,i) = 
  let 
    val _ = print_endline (its i)
    val newtm = mk_tag (list_mk_cA [tm,v1,v2,v3])
    val nfo = lo_walk (0,maxn) newtm in
    if not (isSome nfo) then NONE else 
    let val (nf,n) = valOf nfo in
      (* if can (find_term (C tmem [cS,cK])) nf 
      then NONE 
      else *) SOME (newtm,nf,n)
    end
  end

fun create_targetl tml = 
  let val targetl = List.mapPartial (create_board 1000) (number_snd 0 tml) in
    dict_sort (compare_third Int.compare) 
      (mk_fast_set board_compare targetl)
  end

val targetdir = HOLDIR ^ "/src/AI/experiments/target_combin"
val targetfile =  targetdir ^ "/rewrite-" ^ its version

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

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val head_eval = mk_var ("head_eval", ``:bool -> 'a``)
val head_poli = mk_var ("head_poli", ``:bool -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)
fun tob (tm1,tm2,n) = 
  [tag_heval (mk_eq (tm1,tm2)), tag_hpoli (mk_eq (tm1,tm2))]

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 40}]
val dim = 8
fun dim_head_poli n = [dim,n]

val equality = ``$= : 'a -> 'a -> bool``
val tnnparam = map_assoc (dim_std (1,dim)) [equality,cT,cA,cS,cK,v1,v2,v3] @ 
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]
val dplayer = {tob = tob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleRewrite-combin-" ^ its version, exwindow = 40000,
   ncore = 32, ntarget = 100, nsim = 3200, decay = 1.0}

val rlobj : (board,move) rlobj =
  {
  rlparam = rlparam,
  game = game,
  gameio = gameio,
  dplayer = dplayer
  }

val extsearch = mk_extsearch "mleRewrite.extsearch" rlobj

(*
load "mlReinforce"; open mlReinforce;
load "mleLib"; open mleLib;
load "mleRewrite"; open mleRewrite;
  val tml = cgen_random 2000 (5,15); length tml;
  val targetl = create_targetl tml; length targetl;
  val _ = export_targetl targetl;
val targetl = import_targetd (); length targetl;
val r = rl_start (rlobj,extsearch) targetl;
*)

(* -------------------------------------------------------------------------
   Transformation of problems to ATP goals
   ------------------------------------------------------------------------- *)

fun goal_of_board_eq (tm1,tm2,n) =
  (eq_axl, forall_capital (mk_eq (dest_tag tm1, dest_tag tm2)))

fun goal_of_board_rw (tm1,tm2,n) =
  (rw_axl, forall_capital (mk_cRW (dest_tag tm1, dest_tag tm2)))

fun goal_of_board_ev (tm1,tm2,n) =
  (ev_axl,
    forall_capital (
      list_mk_imp (map (fn x => mk_cL x) [v1,v2,v3],
        mk_cEV (dest_tag tm1, dest_tag tm2))))

(* -------------------------------------------------------------------------
   TPTP export
   ------------------------------------------------------------------------- *)

(*
load "mlReinforce"; open mlReinforce;
load "mleLib"; open mleLib;
load "aiLib"; open aiLib;
load "mleRewrite"; open mleRewrite;
load "hhExportFof"; open hhExportFof;

val tml = cgen_random 100 (10,20); length tml;
val targetl = create_targetl tml; length targetl;
val _ = export_targetl targetl;
val targetd = import_targetd ();
val targetl = dict_sort (compare_third Int.compare) (dkeys targetd);

fun export_goal dir (goal,n) =
  let 
    val tptp_dir = HOLDIR ^ "/src/AI/experiments/TPTP"
    val _ = mkDir_err tptp_dir
    val file = tptp_dir ^ "/" ^ dir ^ "/i/" ^ its n ^ ".p"
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir)
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/i")
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/o")
  in 
    name_flag := false;
    type_flag := false;
    p_flag := false;
    fof_export_goal file goal
  end;

val goall_eq = map goal_of_board_eq targetl;
val _ = app (export_goal "rw-eq") (number_snd 0 goall_eq);
val goall_rw = map goal_of_board_rw targetl;
val _ = app (export_goal "rw-rw") (number_snd 0 goall_rw);
val goall_ev = map goal_of_board_ev targetl;
val _ = app (export_goal "rw-ev") (number_snd 0 goall_ev);
*)


(*
load "mlReinforce"; open mlReinforce;
load "mleLib"; open mleLib;
load "aiLib"; open aiLib;
load "mleRewrite"; open mleRewrite;
load "hhExportFof"; open hhExportFof;

val eq_thml = map ASSUME eq_axl;
val (tm1,tm2,n) = hd targetl;val (l1,t2) = add_time (map (lo_cnorm 100 eq_axl_bare)) l0;
val (l1,t1) = add_time (map (fst o ASM_REWRITE_TAC [])) goall_eq;
val l2 = filter (not o null) l1;

val l0 = map (dest_tag o #1) targetl;
val (l1,t2) = add_time (map (lo_cnorm 100 eq_axl_bare)) l0;
val l2 = filter (not o isSome) l1;

val (l1,t3) = add_time (map (fast_lo_cnorm 100 eq_axl_bare)) l0;
val l2 = filter (not o isSome) l1;
*)


end (* struct *)
