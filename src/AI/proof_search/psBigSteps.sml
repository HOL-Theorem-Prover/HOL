(* ========================================================================= *)
(* FILE          : psBigSteps.sml                                            *)
(* DESCRIPTION   : Successions of non-backtrackable moves chosen after one   *)
(*                 MCTS call for each step                                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure psBigSteps :> psBigSteps =
struct

open HolKernel Abbrev boolLib aiLib psMCTS smlParallel

val ERR = mk_HOL_ERR "psBigSteps"

val temp_flag = ref true

(* -------------------------------------------------------------------------
   Type for examples and distribution derived from a policy
   ------------------------------------------------------------------------- *)

type 'a rlex = ('a * real list) list

(* -------------------------------------------------------------------------
   Tree re-use
   ------------------------------------------------------------------------- *)

fun cut_tree i tree = case tree of
    Leaf  => raise ERR "cut_tree" "leaf"
  | Node (_,ctreev) => !(#3 (Vector.sub (ctreev,i)))

fun erase_tree tree = case tree of
    Leaf  => raise ERR "erase_tree" "leaf"
  | Node (_,ctreev) => 
    let fun f v = let val r = #3 v in r := Leaf end in
      Vector.app f ctreev
    end

(* -------------------------------------------------------------------------
   Big steps and example extraction
   ------------------------------------------------------------------------- *)

fun nvisit tree = case tree of
    Leaf => 0.0
  | Node (node,ctreev) => !(#vis node)

fun mk_dis tree = case tree of
    Leaf => raise ERR "mk_dis" "leaf"
  | Node (node,ctreev) => 
  let
    fun f i (a,b,c) = ((a,i),nvisit (!c))
    val pol = mapi f (vector_to_list ctreev) 
    val _ = if null pol then raise ERR "mk_dis" "pol" else ()
    val tot = sum_real (map snd pol)
    val _ = if tot < 0.5 then raise ERR "mk_dis" "tot" else ()
  in
    (pol,tot)
  end

fun select_bigstep mctsobj tree =
  let val (dis,_) = mk_dis tree in
    if !temp_flag then select_in_distrib dis else best_in_distrib dis
  end 

(* -------------------------------------------------------------------------
   Extracting root examples from bigsteps
   ------------------------------------------------------------------------- *)

fun add_rootex game tree rlex = case tree of 
    Leaf => raise ERR "add_rootex" ""
  | Node (root,ctreev) =>  
  let
    val board  = #board root
    val (dis,tot) = mk_dis tree
    val eval = !(#sum root) / !(#vis root)
    (* todo: use the final eval instead *)
    fun f1 ((m,_),r) = (m,r/tot)
    val poli1 = map f1 dis
    val poli2 = dnew (#move_compare game) poli1
    fun f2 m = dfind m poli2 handle NotFound => 0.0
  in
    (board, eval :: (map f2 (#movel game))) :: rlex
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

fun loop_bigsteps mctsobj rlex tree = case tree of
    Leaf => (false, rlex)
  | Node (root,ctreev) =>  
  let
    val {mctsparam,game,player} = mctsobj
    val {board,stati,...} = root
    val _ = debug ("Board " ^ its (length rlex))
    val _ = debug (#string_of_board game board)
  in
    if not (is_undecided stati) then (is_win stati, rlex) else
    let
      val _ = mcts mctsobj tree
      val (move,i) = select_bigstep mctsobj tree
      val _ = debug ("Move " ^ #string_of_move game move)
      val newrlex = add_rootex game tree rlex
      val newtree = cut_tree i tree
      val _ = erase_tree tree 
      (* try to free up the memory *)
    in
      loop_bigsteps mctsobj newrlex newtree
    end
  end

fun run_bigsteps (tempb,mctsobj) target =
  let
    val _ = temp_flag := tempb
    val tree = starting_tree mctsobj target
  in
    loop_bigsteps mctsobj [] tree
  end

(* -------------------------------------------------------------------------
   Toy example (same as in psMCTS)
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "psBigSteps"; open psBigSteps;

val mctsparam =
  {time = (NONE : real option), nsim = (SOME 10 : int option),
   explo_coeff = 2.0,
   noise = false, noise_coeff = 0.25, noise_gen = gamma_noise_gen 0.2};

val mctsobj : (toy_board,toy_move) mctsobj =
  {mctsparam = mctsparam, game = toy_game, player = random_player toy_game};

val target = (0,10,100);
val _ = debug_flag := true;
val ((winb,rlex),t) = add_time (run_bigsteps (false,mctsobj)) target;
*)

end (* struct *)
