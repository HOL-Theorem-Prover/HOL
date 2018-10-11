(* ========================================================================== *)
(* FILE          : tttRL.sml                                                  *)
(* DESCRIPTION   : Reinforcement learning: MCTS + treeNN for tactics.         *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttRL :> tttRL =
struct
 
open HolKernel boolLib Abbrev tttTools tttNN tttNNtree tttMCTS 

val ERR = mk_HOL_ERR "tttRL"
val dbg = dbg_file "tttRL"

(*
  ---------------------------------------------------------------------------
  Conditions for the game to be over.
  --------------------------------------------------------------------------- *)

fun tac_is_win pos = case pos of
    (true, NONE) => true 
  | (false, SOME []) => true
  | _ => false

fun tac_is_lose pos = case pos of   
    (false, NONE) => true
  | _ => false

fun tac_endcheck r =
       if tac_is_win r  then Win 
  else if tac_is_lose r then Lose 
                        else InProgress

(*
  ---------------------------------------------------------------------------
  TacticToe: statistics
  --------------------------------------------------------------------------- *)

datatype summary_t = 
  WinS | 
  LoseS | 
  Stats of (goal list * real * real * (string * real) list) 

(*
fun proof_of_node tree (node: goal node) =
       if tac_is_win (#pos node)  then SOME WinS
  else if tac_is_lose (#pos node) then SOME LoseS
  else if not (fst (#pos node))   then NONE 
  else
    let
      val gl   = valOf (snd (#pos node))
      val pol1 = first_n 2 
        (dict_sort compare_rmax (trainpoli_of_node tree node))
      val pol2 = map_snd percent pol1
      val eval = percent (traineval_of_node node)
    in
      SOME (Stats (gl, !(#vis node), eval, pol2))
    end
*)

(*
fun summary_of_tree tree = 
  let
    val nodel   = main_variation tree
    val proof   = List.mapPartial (proof_of_node tree) nodel
    val trainex = trainex_of_node tree (dfind [0] tree)
  in
    (proof,trainex)
  end
*)

(*
  ---------------------------------------------------------------------------
  TacticToe: evalpoli
  --------------------------------------------------------------------------- *)


fun randplayer2 movel pid pos =
  let 
    val (eval,prepoli) = rand_evalpoli movel pos 
    val poli = combine (movel, prepoli)
  in
    (if tac_is_win pos then 1.0 else eval, wrap_poli pid poli)
  end

fun player1 preevalpoli movel pid pos =
  let 
    val (eval,prepoli) = preevalpoli pos 
    val poli = combine (movel,prepoli)
  in
    (if tac_is_win pos then 1.0 else eval, wrap_poli pid poli)
  end

fun tac_build_evalpoli preevalpoli p1movel pid pos = case pos of
    (true,NONE)     => (1.0,[]) 
  | (false,NONE)    => (0.0,[]) 
  | (false, SOME l) => 
    randplayer2 (List.tabulate (length l,int_to_string)) pid pos
  | (true, SOME l)  => 
    player1 preevalpoli p1movel pid pos

(*
  ---------------------------------------------------------------------------
  Tactics
  --------------------------------------------------------------------------- *)


fun tac_apply_move tacdict move pos = case pos of
    (_, NONE) => raise ERR "tac_apply_move" "1"
  | (false, SOME gl) =>
    (true, SOME [List.nth (gl, string_to_int move)]) 
  | (true,  SOME gl) =>
    (
    if not (dmem move tacdict) then raise ERR "tac_apply_move" "2" else 
      let 
        val newglno = 
          let val newgl = fst ((dfind move tacdict) (hd gl)) in
            SOME newgl
          end
          handle _ => NONE
      in
        (false, newglno)
      end
    )

fun tac_createdict thml = 
  let 
    fun f i (name,x) = (name, CHANGED_TAC (PURE_ONCE_REWRITE_TAC [x]))
    val tacl = ("REFL", CHANGED_TAC REFL_TAC) :: mapi f thml
  in
    dnew String.compare tacl
  end 

(*
  ---------------------------------------------------------------------------
  Search wrappers
  --------------------------------------------------------------------------- *)

fun tac_mcts_aux fevalpoli tacdict nsim cj =
  let
    val goal       = ([],cj)
    val startpos   = (true, SOME [goal])
    val apply_move = tac_apply_move tacdict
  in
    mcts nsim fevalpoli tac_endcheck apply_move startpos
  end

fun tac_mcts fevalpoli tacdict nsim cj = 
  let val tree = tac_mcts_aux fevalpoli tacdict nsim cj in
    (cj,tree)
  end

fun id_of_move (node: 'a node) move =
  #3 (valOf (List.find (fn x => #1 x = move) (#pol node)))

(* 
   todo: 
   + clarify this code 
   + choose move according to probability and not only best move 
   + train without history in the top node but choose the best move
     that does not loop when computing next move.
*)
fun play_n_move n treel fevalpoli tacdict nsim cj = 
  let 
    val tree = tac_mcts_aux fevalpoli tacdict nsim cj 
    val node = dfind [0] tree
    val pos  = (#pos node)
  in  
    if tac_is_win pos orelse tac_is_lose pos then (rev treel) else
    if n = 0 then (rev ((cj,tree) :: treel)) else
    let 
      val poli = dict_sort compare_rmax (trainpoli_of_node tree node)
      val id    = id_of_move node (fst (hd poli)) 
      val newcj = 
        (list_mk_imp o hd o valOf o snd o #pos o dfind id) tree
    in
      play_n_move (n-1) ((cj,tree) :: treel) fevalpoli tacdict nsim newcj
    end 
    handle _ => (rev ((cj,tree) :: treel))  
  end
 
fun won_tree tree = exists (tac_is_win o #pos) (map snd (dlist tree))

fun trainset_of cjtreel = 
  let fun f (cj,tree) = (cj, trainex_of_node tree (dfind [0] tree)) in
    map f cjtreel
  end

(*
  ---------------------------------------------------------------------------
  Train for n generation
  --------------------------------------------------------------------------- *)

fun norm_vect v = Vector.map (fn x => 2.0 * (x - 0.5)) v
fun denorm_vect v = Vector.map (fn x => 0.5 * x + 0.5) v

fun prepare_trainset trainset =
  let fun f (cj,(eval,poli)) = 
    (order_subtm cj, norm_vect (Vector.fromList (eval :: poli)))
  in
    map f trainset
  end

fun preevalpoli_tm treenn tm = 
  let 
    val (_,fpdatal) = fp_treenn treenn (order_subtm tm)
    val v = denorm_vect (#outnv (last fpdatal))
    val l = tttMatrix.vector_to_list v
  in
    (hd l, map (fn x => x + 0.02) (tl l))
  end

fun preevalpoli treenn pos = case pos of
    (true, SOME [g]) => preevalpoli_tm treenn (list_mk_imp g)
  | _                => raise ERR "preevalpoli1" ""

fun string_of_trainset trainset =
  let 
    fun cmp (x,y) = Real.compare (fst (snd x),fst (snd y))
    val l = dict_sort cmp trainset
    fun sr x = Real.toString (approx 2 x)
    fun f (cj,(eval,poli)) =
      term_to_string cj ^ ": " ^ sr eval ^ "\n  " ^
      String.concatWith " " (map sr poli)
  in
    String.concatWith "\n" (map f l)
  end

fun train_ngen ntot cal tacdict nsim epochn dim bsize cjl =
  let
    val poln = length (dkeys tacdict)
    val movel = dkeys tacdict
    fun loop n trainset treenn =
      if n <= 0 then (treenn,trainset) else
      let
        fun fevalpoli pid pos = 
          tac_build_evalpoli (preevalpoli treenn) movel pid pos 
        val _ = print_endline ("MCTS " ^ int_to_string n)
        fun search i cj = 
          (if i mod 10 = 0 then print_endline (int_to_string i) else ();
           play_n_move 10 [] fevalpoli tacdict nsim cj)
        val cjtreell = mapi search cjl
        val nsolved = length (filter won_tree (mapfilter (snd o hd) cjtreell))
        val _ = 
          append_endline (tactictoe_dir ^ "/rl/summary")
          (int_to_string n ^ ": " ^ int_to_string nsolved)
        val newtrainset = trainset_of (List.concat cjtreell)
        val _ = writel (tactictoe_dir ^ "/rl/trainset" ^ int_to_string n)
          [string_of_trainset newtrainset]
        val _ = print_endline ("NN " ^ int_to_string n)
        val randtreenn = random_treenn dim cal poln
        val trainedtreenn =
          let val prepset = prepare_trainset newtrainset in
            train_treenn_nepoch epochn dim randtreenn bsize prepset  
          end
        val _ = writel (tactictoe_dir ^ "/rl/treenn" ^ int_to_string n)
                [string_of_treenn trainedtreenn]
        val learnedmap = map_assoc (preevalpoli_tm trainedtreenn) cjl;
        val _ = writel (tactictoe_dir ^ "/rl/learnedmap" ^ int_to_string n)
          [string_of_trainset learnedmap]
      in
        loop (n-1) newtrainset trainedtreenn
      end
  in
    loop ntot [] (random_treenn dim cal poln)
  end

(*
load "tttRL"; load "holyHammer"; load "tttSyntEval"; load "tttNN";
open tttRL; open tttTools; open holyHammer; open tttSynt; open tttSyntEval;
open tttNN;
val ERR = mk_HOL_ERR "tttRL";
val _ = erase_file (tactictoe_dir ^ "/rl/summary");

(* Axioms *)
val ax1 = ``PRE 0 = 0``;
val ax2 = ``PRE (SUC x) = x``;
val ax3 = ``(SUC x = SUC y) ==> (x = y)``; 
val ax4 = ``x + 0 = x``;
val ax5 = ``x + SUC y = SUC (x + y)``;
val ax6 = ``x * 0 = 0``;
val ax7 = ``x * (SUC y) = (x * y) + x``;
fun hhprove tm = TAC_PROOF (([],tm), (holyhammer tm));
val thml = map (fn (a,b) => (a, hhprove b)) 
  [("PRE_0",ax1),("PRE_S",ax2),
   ("ADD_0",ax4),("ADD_S",ax5),
   ("MUL_0",ax6),("MUL_S",ax7)];

val symthml = map (fn (a,b) => ("SYM_" ^ a, GSYM (hhprove b))) 
  [("PRE_S",ax2),("ADD_S",ax5),("MUL_S",ax7)];

val allthml = thml @ symthml;
val tacdict = tac_createdict allthml;
val movel = dkeys tacdict;
val poln = dlength tacdict;

(* Conjecturing *)
val run_id = "conjecturing";
val _ = ttt_synt_dir := tactictoe_dir ^ "/log_synt/" ^ run_id;
val _ = cleanDir_rec (!ttt_synt_dir);
val cl = List.concat (map (find_terms is_const) [ax1,ax2,ax4,ax5,ax6,ax7]);
val cset = mk_fast_set Term.compare cl;
fun filterf n tml = first_n n (shuffle tml)
val cjll = shuffle (cjenum 7 100000 filterf cset);

fun success_tac2 tac goal = let val (l,_) = tac goal in null l end;
fun is_proved2 cj = success_tac2 (REWRITE_TAC (map snd thml)) ([], cj);
val cjpl = filter is_proved2 cjl;

(* Treenn *)
val dim = 11;
val arity = [2,2,0,2,1,1];
val cal = combine (cset,arity);
val bsize = 32; val epochn = 100; 
val _ = learning_rate := 0.01;

(* MCTS *)
val nsim = 1600;
val (treenn,trainset) = 
  train_ngen 10 cal tacdict nsim epochn dim bsize cjpl;


val winl = filter variation_win (fst result);
length cjpl;
length winl;

val trainsetorg' = dict_sort compare_rmax (map_snd fst trainsetorg);

(* Look at the evaluation of the nn *)
val evall = map_assoc (fst o preevalpoli_tm treenn) cjl;
val evalsorted = dict_sort compare_rmax evall;



(* todo *)
  Print summary of the results at each generation.
  Weight update can't be larger than (learning_rate times 1).

val INDUCT_TAC = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC;


5) Produce conjectures that have a probability of 
     
  6) Use the prior evaluation to chose one of the possibility.
     Use tactics that produces disjunctions of multiple goals.
     Recognizing a disjunction and choose the right dijsunct (player 1).

  1) Do experiments with arbitrary size 20 formulas. 


50 percent of being provable by the current NN.
     
*)

end (* struct *)
