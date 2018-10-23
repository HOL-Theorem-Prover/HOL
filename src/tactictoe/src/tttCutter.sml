(* ========================================================================== *)
(* FILE          : tttCutter.sml                                                  *)
(* DESCRIPTION   : Theorem prover based on cut introduction seen as a 2 player game. *)
(* Player 1 tries to prove the goal. *)
(* Player 2 prevents player1 from proving the goal.         *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttCutter :> tttCutter =
struct
 
open HolKernel boolLib Abbrev tttTools tttNN tttNNtree tttMCTS tttSynt

val ERR = mk_HOL_ERR "tttCutter"
val dbg = dbg_file "tttCutter"


(* Tools *)
fun dset cmp l = dnew cmp (map (fn x => (x,())) l)
fun has_boolty x = type_of x = bool
fun eval_treenn treenn x = fst (apply_treenn treenn x)

(*
  ---------------------------------------------------------------------------
  Board + move
  --------------------------------------------------------------------------- *)

(* move *)
datatype cutter_move = Forget of goal | Cut of term | Choice of goal 

fun dest_cutmove x = case x of
    Cut tm => tm
  | _      => raise ERR "dest_cutmove" ""

fun dest_choicemove x = case x of
    Choice g => g
  | _        => raise ERR "dest_choicemove" ""


(* board *)
datatype cutter_board = 
  Board1 of goal | Board2 of goal list

fun dest_board1 x = case x of
    Board1 g => g
  | _        => raise ERR "dest_board1" ""

fun dest_board2 x = case x of
    Board2 gl => gl
  | _         => raise ERR "dest_board2" ""


(* starting position *)
fun cutter_mk_startpos cj = (true, Board1 ([],cj))

(*---------------------------------------------------------------------------
  Policy and evaluation
  ---------------------------------------------------------------------------*)

fun singleton a = [a]
val goal_of_p1pos  = dest_board1 o snd
fun goal_of_p1node (node:(cutter_board,cutter_move) node) = 
  node |> #pos |> goal_of_p1pos

(* Player 1 *)
fun p1eval judgetnn pos =
  let val tm = (goal_to_nnterm o goal_of_p1pos) pos in
    eval_treenn judgetnn tm
  end

(* cut synthesis *)
fun relative_eval gentnn casterl input tm =
  let val iotm = io_to_nnterm (input, cast_to_bool casterl tm) in
    eval_treenn gentnn iotm
  end


fun p1cut_one threshold (cset,casterl) gentnn input =
  let
    fun evalf tm    = relative_eval gentnn casterl input tm
    fun filterf tml = evalf_to_filterf threshold evalf tml
  in
    synthetize filterf (10,20) cset
  end

(* hacky function that guarantees the policy is not empty *)
fun p1cut (cset,casterl) gentnn input =
  let
    fun loop pl l = case l of 
       [] => pl
     | a :: m => 
      let val result = p1cut_one a (cset,casterl) gentnn input in 
        if length result < 2 then loop result m else result
      end
  in
    loop [] [0.01, ~1.0]
  end


fun mk_forgetl acc (asm,w) = case asm of
    []     => []
  | a :: m => (acc @ m,w) :: mk_forgetl (acc @ [a]) (m,w) 
  

fun p1poli (cset,casterl) (judgetnn,gentnn) pos =
  let
    val goal         = goal_of_p1pos pos
    val input        = goal_to_nnterm goal
    fun evalf tm     = relative_eval gentnn casterl input tm
    val cutl         = p1cut (cset,casterl) gentnn input
    val cutpoli      = map (fn x => (Cut x, evalf x)) cutl
    fun evalforget x = eval_treenn judgetnn (goal_to_nnterm x)
    val forgetl      = mk_forgetl [] goal
    val forgetpoli   = map (fn x => (Forget x, evalforget x)) forgetl 
  in
    forgetpoli @ cutpoli
  end

fun p1evalpoli (cset,casterl) (judgetnn,gentnn) pos =
  (p1eval judgetnn pos, p1poli (cset,casterl) (judgetnn,gentnn) pos)

(* Player 2 *)
fun p2evalpoli judgetnn pos =
  let  
    val gl   = pos |> snd |> dest_board2 
    fun f g  = eval_treenn judgetnn (goal_to_nnterm g)
    val poli = map (fn g => (Choice g, f g)) gl
    val eval = snd (hd (dict_sort compare_rmin poli))
               handle Empty => raise ERR "p2evalpoli" ""
  in
    (eval,poli)
  end

(* Player 1 + Player 2 *)
fun cutter_fevalpoli (cset,casterl) (judgetnn,gentnn) pos =
  if fst pos 
  then p1evalpoli (cset,casterl) (judgetnn,gentnn) pos
  else p2evalpoli judgetnn pos

(*---------------------------------------------------------------------------
  Status
  ---------------------------------------------------------------------------*)

fun is_refl (_,w) = 
  is_eq w andalso (let val (a,b) = dest_eq w in a = b end)
fun is_inst tm (_,w) = can (match_term tm) w

fun is_subs_aux (tm1,tm2) tm3 =
  let
    val (th1,th2,th3) = (mk_thm ([],tm1), mk_thm ([],tm2), mk_thm ([],tm3)) 
  in
    if mem tm3 [tm2,tm1] then false else
    let 
      val red   = lhs (concl th1)
      val occl  = find_terms (fn x => x = red) (concl th2)
      fun f i _ = SUBS_OCCS [([i+1],th1)] th2 
      val subl  = mapi f occl
    in
      mem tm3 (map concl subl)
    end
  end
  handle _ => false

fun is_subs (asl,w) =
  exists (fn x => is_subs_aux x w) (cartesian_product asl asl)

fun is_apterm g =
  let val pretm = (snd o only_hd o fst o AP_TERM_TAC) g in
    mem pretm (fst g)
  end
  handle _ => false

fun is_primitive axl g =
  exists (fn x => is_inst x g) axl orelse
  is_refl g orelse
  is_subs g orelse
  is_apterm g

fun cutter_status_of axl tree pos =
  if not (fst pos) then Undecided else 
    if is_primitive axl (dest_board1 (snd pos)) 
    then Win 
    else Undecided

(*---------------------------------------------------------------------------
  Move application
  ---------------------------------------------------------------------------*)

(* player 1*)
fun apply_cut tm (asl,w) = [(asl,tm),(tm::asl,w)] 

fun p1_apply_move move g = case move of
    Cut tm    => (false, Board2 (apply_cut tm g)) 
  | Forget g => (true, Board1 g)
  | _         => raise ERR "p1_apply_move" ""

(* player 2 *)
fun p2_apply_move move gl = (true, Board1 (dest_choicemove move))

fun cutter_apply_move move pos = case pos of
    (true, Board1 g)   => p1_apply_move move g
  | (false, Board2 gl) => p2_apply_move move gl
  | _ => raise ERR "apply_move" ""


(*---------------------------------------------------------------------------
  Analysis of the result
  ---------------------------------------------------------------------------*)

datatype wintree = Wleaf of int list | Wnode of (int list * wintree list)

fun winning_tree tree id =
  let 
    val node  = dfind id tree 
    val cidl0 = map snd (#pol node)
    fun is_win cid = 
      (#status (dfind cid tree) = Win handle NotFound => false)
    val cidl1 = filter is_win cidl0
  in
    if null cidl1 
    then Wleaf id 
      else Wnode (id, map (winning_tree tree) cidl1)
  end

(*---------------------------------------------------------------------------
  Preparation of the training examples
  ---------------------------------------------------------------------------*)

val cutoff = 49.999

fun add_empty_poli l = map (fn (a,b) => (a,(b,[]:real list))) l

fun ln_duplicate (g,(x,best)) = 
  let val n = Real.floor (Math.ln (1.0 + x / cutoff) + 1.0) in
    duplicate n [(g,best)]
  end

(* judgetnn *)
fun is_nodetrain (node : (cutter_board, cutter_move) node) =
  #status node = Win orelse #vis node > cutoff

fun train_of_tree tree = filter is_nodetrain (map snd (dlist tree))

fun judge_trainex (node : (cutter_board, cutter_move) node) = 
   case #pos node of
    (true, Board1 g) => SOME (g, (#vis node, #sum node / #vis node))
  | _                => NONE

fun max_score l =
  let val (a,b) = split l in 
    (sum_real a, (last (dict_sort Real.compare b))) 
  end

fun prepare_judgetnn_data cjpl =
  let 
    val nodel = List.concat (map (train_of_tree o snd) cjpl)
    val l0    = List.mapPartial judge_trainex nodel
    val l1    = map_fst goal_to_nnterm l0
    val d     = dregroup Term.compare l1
    val l2    = map_snd max_score (dlist d)
    val l3    = List.concat (map ln_duplicate l2)
  in
    l3
  end

(* gentnn *)
fun interesting_polie (tree : (cutter_board, cutter_move) tree) 
  (g,(move,cid)) =
  if not (dmem cid tree) then NONE else
  let val node = dfind cid tree in
    if (#vis node > cutoff)
    then SOME ((g,move), (#vis node, #sum node / #vis node))
    else NONE
  end

fun extract_poli (node : (cutter_board, cutter_move) node) =
  (
  dest_board1 (snd (#pos node)), 
  mapfilter (fn ((move,_),cid) => (dest_cutmove move, cid)) (#pol node)
  )

fun distrib_poli (g,l) = map (fn x => (g,x)) l

fun gen_trainex tree =
  let 
    val nodel0 = map snd (dlist tree)
    val nodel1 = filter (fst o #pos) nodel0
    val polil0 = mapfilter extract_poli nodel1
    val polil1 = List.concat (map distrib_poli polil0)
  in
    List.mapPartial (interesting_polie tree) polil1
  end

fun weighted_average l = 
  let 
    val tot = sum_real (map fst l)
    val sum = sum_real (map (fn (a,b) => a * b) l)
  in
    (tot, sum / tot)
  end

fun subterms_of tm = find_terms (fn _ => true) tm

fun prepare_gentnn_data casterl cjpl =
  let
    fun gt_to_term (g,t) = 
      io_to_nnterm (goal_to_nnterm g, cast_to_bool casterl t)
    val l0 = List.concat (map gen_trainex (map snd cjpl))
    fun f ((a,b),c) = map (fn x => ((a,x),c)) (subterms_of b)
    val l1 = List.concat (map f l0)
    val l2 = map_fst gt_to_term l1
    val d  = dregroup Term.compare l2
    val l3 = map_snd weighted_average (dlist d)
    val l4 = List.concat (map ln_duplicate l3)
  in
    l4
  end

(*---------------------------------------------------------------------------
  Training wrapper
  ---------------------------------------------------------------------------*)

fun wrap_train_treenn fullcal trainset =
  let
    val bsize    = 3
    val dim      = 5
    val schedule = [(30,0.01)]
    val prepset  = prepare_trainset (add_empty_poli trainset)
    val treenn   = random_treenn (dim,0) fullcal
  in
    train_treenn_schedule dim treenn bsize prepset schedule
  end

(*---------------------------------------------------------------------------
  MCTS wrapper
  ---------------------------------------------------------------------------*)

fun mcts_targetl nsim (cset,casterl) (judgetnn,gentnn) axl targetl =
  let fun f i target =
    let
      val _    = 
        print_endline (int_to_string i ^ ": " ^ term_to_string target)  
      val fevalpoli  = cutter_fevalpoli (cset,casterl) (judgetnn,gentnn)
      val status_of  = cutter_status_of axl
      val apply_move = cutter_apply_move
      val tree =
        mcts nsim fevalpoli status_of apply_move (cutter_mk_startpos target)
      val status = #status (dfind [0] tree)
    in
      print_endline (" " ^ string_of_status status);
      (target,tree)
    end
  in
    mapi f targetl
  end


(*---------------------------------------------------------------------------
  Statistics
  ---------------------------------------------------------------------------*)

fun is_nodewin (node : (cutter_board, cutter_move) node) = 
  #status node = Win

fun is_treewin (tree : (cutter_board, cutter_move) tree) = 
  is_nodewin (dfind [0] tree)

fun success_rate l =
  let val winl = map fst (filter (is_treewin o snd) l) in
    length winl
  end


(* test 
load "tttCutter"; 
open tttTools tttMCTS tttCutter tttNNtree tttSynt;

(* signature *)
val cj   = ``0 = 0 + 0`` ;
val typical_input = io_to_nnterm (goal_to_nnterm ([cj,cj],cj), cj);
val casterl = create_boolcastl [typical_input];
val cal = cal_of_term typical_input;
val fullcal = map (fn x => (x,1)) casterl @ cal;
val cset = mk_fast_set Term.compare (find_terms is_const cj);

(* starting nn *)
val judgetnn  = random_treenn (5,0) fullcal;
val gentnn    = random_treenn (5,0) fullcal;

(* axioms *)
val ax4 = ("ADD_0", ``x + 0 = x``);
val ax5 = ("ADD_S", ``x + SUC y = SUC (x + y)``);
val axl = map snd [ax4];


(* Targets *)
fun filterf l = first_n 100 (shuffle l);
val targetl = synthetize filterf (100,20) cset;

(* MCTS *)
val nsim = 1600;

val targetl = synthetize filterf (100,20) cset;



val generation1 = success_rate cjpl0;

(* Training *)

mcts_targetl nsim (cset,casterl) (judgetnn,gentnn) axl targetl

(* judgetnn *)


val rand_judgetnn = random_treenn (dim,0) fullcal;
val new_judgetnn =
  train_treenn_schedule dim rand_judgetnn bsize judge_train2 schedule;

(* gentnn *)
fun train


val gen_trainset = prepare_judgetnn_data cjpl;
val schedule     = [(30,0.01)];

val rand_gentnn = random_treenn (dim,0) fullcal;
val new_gentnn  =
  

(* start again *)

val nsim = 16000;
val new_fevalpoli = cutter_fevalpoli (cset,casterl) (new_judgetnn,new_gentnn);
fun new_mcts_tree i cj =
  (
  init_caches ();
  print_endline (int_to_string i ^ ": " ^ term_to_string cj);
  (cj,mcts nsim new_fevalpoli status_of apply_move (cutter_mk_startpos cj))
  )
val cjpl_generation2 = mapi new_mcts_tree targetl;

val generation2 = success_rate cjpl_generation2;

(* todo *)
4) print out training set learnedmap , proofs when they exists.
   print debugging information about the quality of training set 
   (mean variance, etc)

5) Do a 10 steps reinforcement learning loop. (10 hours)


(* todo later *)
2) add caches to limit inefficiency.

3) probably just memorize the policy for one goal then the size 
   is just the number of tree.
3) add time monitoring too.

*)


(*
fun is_p1node (node  = fst (#pos node)

fun is_loopcut tree id g (tml,_) =
  let 
    val idl    = genealogy id
    val nodel0 = map (fn x => dfind x tree) idl
    val nodel1 = filter is_p1node nodel0
    val pgl    = map goal_of_p1node nodel1
    val gl     = apply_cut tml g
  in
    exists (fn x => dmem x (list_to_dict goal_compare pgl)) gl 
  end
*)


(*
  ---------------------------------------------------------------------------
  Creating a training set for a neural network to learn from.
  (probably not part of mcts file)
  --------------------------------------------------------------------------- *)

(*
fun traineval_of_node node = #sum node / #vis node

fun trainpoli_of_decision tree vtot ((move,_),cid) =
  let 
    val node   = dfind cid tree
    val vis    = #vis node
    val polisc = 
  in
      if win node then 1.0 else
    if lose node then (move, 0.0) else 
    else SOME (move, vis / vtot)
  end
  handle NotFound => NONE

fun trainpoli_of_node tree node = 
  map (trainpoli_of_child tree (!(#vis node))) (#pol node)

fun trainex_of_node tree (node: 'a node) =
  (traineval_of_node node, map snd (trainpoli_of_node tree node))
*)


end (* struct *)
