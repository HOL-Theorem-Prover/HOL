(* ========================================================================= *)
(* FILE          : psBigSteps.sml                                            *)
(* DESCRIPTION   : Succession of non-backtrackable moves chosen after one    *)
(*                 MCTS call for each step                                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure psBigSteps :> psBigSteps =
struct

open HolKernel Abbrev boolLib aiLib psMCTS

val ERR = mk_HOL_ERR "psBigSteps"

(* -------------------------------------------------------------------------
   Parameters     
   ------------------------------------------------------------------------- *)

type ('a,'b) bigstepsparam =
  {
    mcts_param : ('a,'b) mctsparam,
    temp_flag : bool, 
    max_bigsteps : 'a -> int,
    verbose : bool,
    (* these four should be moved to mctsparam or extended param *)
    string_of_move : 'b -> string,
    movel : 'b list,
    move_compare : ('b * 'b) -> order,
    string_of_board : 'a -> string
  }

(* -------------------------------------------------------------------------
   Type for examples and distribution derived from a policy 
   ------------------------------------------------------------------------- *)

type 'a ex = ('a * real list * real list)
type 'b dis = ((('b * real) * id) * real) list

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
    fun change_node (x,{pol,board,sum,vis,status}) =
      (rm_suffix id x, 
        {pol=map_snd (rm_suffix id) pol,
         board=board,sum=sum,vis=vis,status=status})
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

fun print_distrib g l =
  let
    fun f1 (((move,r),_),_) = g move ^ " " ^ (rts (approx 4 r))
    fun f2 (((move,_),_),r) = g move ^ " " ^ (rts (approx 4 r))
  in
    print_endline ("  Prior Policy: " ^ String.concatWith ", " (map f1 l));
    print_endline ("  Visits:       " ^ String.concatWith ", " (map f2 l))
  end

fun select_bigstep param tree =
  let
    val (d,_) = make_distrib tree
    val choice =
      if #temp_flag param 
      then select_in_distrib d 
      else best_in_distrib d
  in
    (snd choice, d)
  end

(* -------------------------------------------------------------------------
   Extracting root examples from bigsteps
   ------------------------------------------------------------------------- *)

fun complete_pol param mrl =
  let
    val d = dnew (#move_compare param) mrl
    fun f move = dfind move d handle NotFound => 0.0
  in
    map f (#movel param)
  end

fun add_rootex param tree exl =
  let
    val root = dfind [] tree
    val board  = #board root
    val (dis,tot) = make_distrib tree
    val eval = #sum root / #vis root
    val poli = map (fn (((move,_),_),r) => (move,r / tot)) dis
  in
    (board, [eval], complete_pol param poli) :: exl
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

fun debug_board param board = 
  if #verbose param
  then print_endline ((#string_of_board param) board)
  else ()

fun debug_dis param dis =
  if #verbose param
  then print_distrib (#string_of_move param) dis
  else ()

(* rootl and exl are reversed *)
fun loop_bigsteps (n,nmax) param (exl,rootl) tree =
  let
    val board = #board (dfind [] tree)
    val status = #status_of (#mcts_param param) board
    val _ = debug_board param board
  in
    if status <> Undecided orelse n >= nmax 
      then (status = Win,exl,rootl) else
    let
      val newtree = mcts (#mcts_param param) tree
      val root = dfind [] newtree
      val (cid,dis) = select_bigstep param newtree
      val _ = debug_dis param dis
      val cuttree = 
        if #noise_flag (#mcts_param param)
        then starttree_of (#mcts_param param) (#board (dfind cid newtree))
        else cut_tree cid newtree
      val newexl = add_rootex param newtree exl
      val newrootl = root :: rootl
    in
      loop_bigsteps (n+1,nmax) param (newexl,newrootl) cuttree
    end
  end

fun run_bigsteps param target =
  let
    val tree = starttree_of (#mcts_param param) target
    val n = (#max_bigsteps param) target
  in
    loop_bigsteps (0,n) param ([],[]) tree
  end

(* -------------------------------------------------------------------------
   Toy example (same as in psMCTS)
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "psBigSteps"; open psBigSteps;

type board = int * int;
datatype move = Incr | Decr; 
val movel = [Incr,Decr];

fun status_of ((start,finish):board) = 
  if start >= finish then Win 
  else if start < 0 then Lose else Undecided;
fun apply_move (m:move) ((start,finish):board) = case m of 
   Incr => ((start+1,finish):board)
 | Decr => (start-1,finish);
(* random guidance *)
fun fevalpoli (_:board) = (0.0 , map_assoc (fn _ => 1.0) movel);

val mcts_param : (board,move) psMCTS.mctsparam =
  {
  nsim = 16000, 
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_flag = false,
  noise_coeff = 0.25,
  noise_alpha = 0.2,
  status_of = status_of,
  apply_move = apply_move,
  fevalpoli = fevalpoli
  };

val param : (board,move) psBigSteps.bigstepsparam =
  {
  mcts_param = mcts_param,
  temp_flag = false, 
  max_bigsteps = (fn (a,b) => 2 * b),
  verbose = true,
  string_of_move = PolyML.makestring,
  movel = movel,
  move_compare = 
    (fn (a,b) => String.compare (PolyML.makestring a, PolyML.makestring b)),
  string_of_board = PolyML.makestring
  };

val target = (0,10);
val _ = run_bigsteps param target;
val (winb,exl,rootl) = run_bigsteps param target;
*)

end (* struct *)
