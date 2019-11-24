(* ========================================================================= *)
(* FILE          : psBigSteps.sml                                            *)
(* DESCRIPTION   : Succession of non-backtrackable moves chosen after one    *)
(*                 MCTS call for each step                                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure psBigSteps :> psBigSteps =
struct

open HolKernel Abbrev boolLib aiLib psMCTS smlParallel

val ERR = mk_HOL_ERR "psBigSteps"

(* -------------------------------------------------------------------------
   Type for examples and distribution derived from a policy
   ------------------------------------------------------------------------- *)

type 'a rlex = ('a * real list * real list) list

(* -------------------------------------------------------------------------
   Tree re-use
   ------------------------------------------------------------------------- *)

fun is_prefix l1 l2 = case (l1,l2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => a1 = a2 andalso is_prefix m1 m2

fun is_suffix l1 l2 = is_prefix (rev l1) (rev l2)

fun rm_prefix l1 l2 = case (l1,l2) of
    ([],_) => l2
  | (_,[]) => raise ERR "rm_prefix" "1"
  | (a1 :: m1, a2 :: m2) =>
    (if a1 = a2 then rm_prefix m1 m2 else raise ERR "rm_prefix" "2")

fun rm_suffix l1 l2 = rev (rm_prefix (rev l1) (rev l2))

fun cut_tree id tree =
  let
    val l = filter (fn x => is_suffix id (fst x)) (dlist tree)
    fun change_node (x,{pol,value,board,sum,vis,status}) =
      (rm_suffix id x,
        {pol=map_snd (rm_suffix id) pol,
         board=board, value=value, sum=sum, vis=vis, status=status})
  in
    dnew id_compare (map change_node l)
  end

(* -------------------------------------------------------------------------
   Big steps and example extraction
   ------------------------------------------------------------------------- *)

fun make_distrib tree =
  let
    val pol = #pol (dfind [] tree)
    val _ = if null pol then raise ERR "make_distrib" "pol" else ()
    fun f (_,cid) = #vis (dfind cid tree) handle NotFound => 0.0
    val dis = map_assoc f pol
    val tot = sum_real (map snd dis)
    val _ = if tot < 0.5 then raise ERR "make_distrib" "tot" else ()
  in
    (dis,tot)
  end

fun debug_ep obj mcts_obj dis root =
  if #verbose obj then
  let
    val {game,player,mcts_param} = mcts_obj
    val old_eval = #value root
    val new_eval = #sum root / #vis root
    val fm = #string_of_move game
    fun g r = pad 6 "0" (rts (approx 4 r))
    fun f1 (((move,r),_),_) = fm move ^ " " ^ g r
    fun f2 (((move,_),_),r) = fm move ^ " " ^ g r
  in
    print_endline ("  Old Eval: " ^ g old_eval);
    print_endline ("  New Eval: " ^ g new_eval);
    print_endline ("  Old Policy: " ^ String.concatWith ", " (map f1 dis));
    print_endline ("  New Policy: " ^ String.concatWith ", " (map f2 dis))
  end
  else ()

fun select_bigstep obj mcts_obj tree =
  let
    val (dis,_) = make_distrib tree
    val (_,cid) =
      if #temp_flag obj then select_in_distrib dis else best_in_distrib dis
    val _ = debug_ep obj mcts_obj dis (dfind [] tree)
  in
    cid
  end

(* -------------------------------------------------------------------------
   Extracting root examples from bigsteps
   ------------------------------------------------------------------------- *)

fun complete_pol game mrl =
  let
    val d = dnew (#move_compare game) mrl
    fun f move = dfind move d handle NotFound => 0.0
  in
    map f (#movel game)
  end

fun add_rootex game tree exl =
  let
    val root = dfind [] tree
    val board  = #board root
    val (dis,tot) = make_distrib tree
    val eval = #sum root / #vis root
    val poli = map (fn (((move,_),_),r) => (move,r / tot)) dis
  in
    (board, [eval], complete_pol game poli) :: exl
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

type ('a,'b,'c) bigsteps_obj =
  {
  verbose : bool,
  temp_flag : bool,
  max_bigsteps : 'a -> int,
  precomp : 'a -> 'c,
  preplayer : 'c -> ('a,'b) player,
  game : ('a,'b) game,
  mcts_param : mcts_param
  }

fun debug_board obj game board =
  if #verbose obj
  then print_endline ((#string_of_board game) board)
  else ()

(* rootl and exl are reversed *)
fun loop_bigsteps (n,nmax) cstatus obj mcts_obj (exl,rootl) tree =
  let
    val {mcts_param,game,player} = mcts_obj
    val board = #board (dfind [] tree)
    val status = #status_of game board
    val _ = debug_board obj game board
  in
    if status <> Undecided orelse n >= nmax
      then (status = Win, cstatus = Win, exl, rootl) else
    let
      val endtree = mcts mcts_obj tree
      val root = dfind [] endtree
      val newcstatus = if cstatus = Win then Win else #status root
      val cid = select_bigstep obj mcts_obj endtree
      val newtree = cut_tree cid endtree
      (* if #noise_flag mcts_param then 
         starttree_of mcts_obj (#board (dfind cid endtree)) else *)
      val newexl = add_rootex game endtree exl
      val newrootl = root :: rootl
    in
      loop_bigsteps (n+1,nmax) newcstatus 
        obj mcts_obj (newexl,newrootl) newtree
    end
  end

fun run_bigsteps obj target =
  let
    val precomp = (#precomp obj) target
    val mcts_obj = 
      {
      mcts_param = (#mcts_param obj),
      game = (#game obj),
      player = (#preplayer obj) precomp   
      }
    val tree = starttree_of mcts_obj target
    val n = (#max_bigsteps obj) target
  in
    loop_bigsteps (0,n) Undecided obj mcts_obj ([],[]) tree
  end

(* -------------------------------------------------------------------------
   Toy example (same as in psMCTS)
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "psBigSteps"; open psBigSteps;

val mcts_param =
  {
  nsim = 32000,
  stopatwin_flag = false,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = true, noise_root = false,
  noise_coeff = 0.25, noise_gen = gamma_noise_gen 0.2
  };

val bigsteps_obj : (toy_board,toy_move,unit) bigsteps_obj =
  {
  verbose = true,
  temp_flag = false,
  max_bigsteps = (fn (a,b) => 2*b),
  precomp = (fn _ => ()),
  preplayer = (fn () => uniform_player toy_game),
  game = toy_game,
  mcts_param = mcts_param
  };

val target = (0,10);
val (_,t) = add_time (run_bigsteps bigsteps_obj) target;
val (winb,exl,rootl) = run_bigsteps bigsteps_obj target;
*)

end (* struct *)
