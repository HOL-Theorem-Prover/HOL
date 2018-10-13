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
  if tac_is_win r  then Win  else 
  if tac_is_lose r then Lose else InProgress

fun genealogy id = 
  if null id then [] else id :: genealogy (tl id) 

fun hd_only x = case x of [a] => a | _ => raise ERR "hd_only" ""

fun tac_isloop (tree: goal tree) pid pos = case pos of
    (_, NONE) => false
  | (true, _) => false
  | (false, SOME gl) =>
  let 
    val nodel   = map (fn x => dfind x tree) (genealogy pid)
    val p1nodel = filter (fst o #pos) nodel
    val pgl     = map (hd_only o valOf o snd o #pos) p1nodel
    val gdict   = count_dict (dempty goal_compare) pgl
  in
    exists (fn x => dmem x gdict) gl
  end

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
    mcts nsim fevalpoli tac_endcheck tac_isloop apply_move startpos
  end

fun tac_mcts fevalpoli tacdict nsim cj = 
  let val tree = tac_mcts_aux fevalpoli tacdict nsim cj in
    (cj,tree)
  end

fun id_of_move (node: 'a node) move =
  #3 (valOf (List.find (fn x => #1 x = move) (#pol node)))

(* todo: clarify this code *)

fun play_n_move n treel fevalpoli tacdict nsim cj = 
  let 
    val tree = tac_mcts_aux fevalpoli tacdict nsim cj 
    val node = dfind [0] tree
    val pos  = (#pos node)
  in  
    if tac_is_win pos orelse tac_is_lose pos then (rev treel) else
    if n = 0 then (rev ((cj,tree) :: treel)) else
    let 
      val poli  = trainpoli_of_node tree node        
      val move  = select_in_distrib poli
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
    (hd l, tl l)
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
      term_to_string cj ^ ":\n  " ^ sr eval ^ "\n  " ^
      String.concatWith " " (map sr poli)
  in
    String.concatWith "\n" (map f l)
  end

fun merge_trainset trainset1 trainset2 =
  let 
    val trainsetd2 = dnew Term.compare trainset2
    fun overwritten (cj,_) = dmem cj trainsetd2
    val newtrainset1 = filter (not o overwritten) trainset1
  in
    trainset1 @ trainset2
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
        val addtrainset = trainset_of (List.concat cjtreell)
        val newtrainset = merge_trainset trainset addtrainset
        val _ = 
          print_endline ("trainset size " ^ int_to_string (length newtrainset))
        val _ = writel (tactictoe_dir ^ "/rl/trainset" ^ int_to_string n)
          [string_of_trainset addtrainset]
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
load "tttRL"; load "tttSynt"; load "holyHammer";
open tttRL tttTools holyHammer tttSynt tttNN;
val ERR = mk_HOL_ERR "tttRL";
val _ = clean_dir (tactictoe_dir ^ "/rl");

(* Axioms: robinson *)
val ax1 = ("PRE_0",``PRE 0 = 0``);
val ax2 = ("PRE_S",``PRE (SUC x) = x``);
val ax3 = ("SUC_INJ", ``(SUC x = SUC y) ==> (x = y)``); 
val ax4 = ("ADD_0", ``x + 0 = x``);
val ax5 = ("ADD_S", ``x + SUC y = SUC (x + y)``);
val ax6 = ("MUL_0", ``x * 0 = 0``);
val ax7 = ("MUL_S", ``x * (SUC y) = (x * y) + x``);

val axl = [ax1,ax2,ax4,ax5,ax6,ax7];




fun hhprove tm = TAC_PROOF (([],tm), (holyhammer tm));

val robinson_thml = map (fn (a,b) => (a, hhprove b)) axl;



val symthml = map (fn (a,b) => ("SYM_" ^ a, GSYM (hhprove b))) 
  [("PRE_S",ax2),("ADD_S",ax5),("MUL_S",ax7)];

val allthml = thml;
val tacdict = tac_createdict allthml;
val movel = dkeys tacdict;
val poln = dlength tacdict;

(* Term generation *)
val cl   = List.concat (map (find_terms is_const) [ax1,ax2,ax4,ax5,ax6,ax7]);
val cset = mk_fast_set Term.compare cl;
val ptac = REWRITE_TAC (map snd thml)
val cjpl = uniform_provable ptac 50 cset 20;

(* Treenn *)
val dim = 11;
val arity = [2,2,0,2,1,1];
val cal = combine (cset,arity);
val bsize = 16; val epochn = 100; 
val _ = learning_rate := 0.1;

(* MCTS *)
val nsim = 1600;
val (treenn,trainset) = train_ngen 10 cal tacdict nsim epochn dim bsize cjpl;



(* PA(-) with semiring *)
val pax1  = ("ADD_ASSOC", ``(x+y)+z = x+(y+z)``);
val pax2  = ("ADD_COM",   ``x+y = y+x``);
val pax3  = ("MUL_ASSOC", ``(x*y)*z = x*(y*z)``);
val pax4  = ("MUL_COM",   ``x*y = y*x``);
val pax5  = ("DISTR",     ``(x * (y + z) = (x * y) + (x * z))``);
val pax6  = ax4;
val pax6' = ax6;
val pax7  = ("MUL_1",      ``x * SUC 0 =x``);
val pax8  = ("LE_TRANS",   ``(x < y /\ y < z) ==> x < z``);
val pax9  = ("LE_ANTISYM", ``~(x<x)``);
val pax10 = ("LE_TRICHO",  ``x < y \/ (x = y) \/ y < x``);
val pax11 = ("LE_ADD", ``x < y ==> x + z < y + z``);
val pax12 = ("LE_MUL", ``(0 < z /\ x < y) ==> x * z < y * z``);
val pax13 = ("MIN",    ``x < y ==> (x + (y - x) = y)``);
val pax14 = ("LE_S",   ``0 < SUC 0``);
val pax15 = ("LE_0",   ``~(x = 0) ==> x > 0``);

val paxl = [pax1,pax2,pax3,pax4,pax5,pax6,pax6',pax7,pax8,pax9,pax10] @
 [pax11,pax12,pax13,pax14,pax15];

val peano_thml = map (fn (a,b) => (print_endline a; (a, hhprove b))) paxl;




load "tttRL"; load "tttSynt"; load "holyHammer";
open tttRL tttTools holyHammer tttSynt tttNN tttNNtree;
val ERR = mk_HOL_ERR "tttRL";
val _ = clean_dir (tactictoe_dir ^ "/rl");

val pax1  = ("ADD_ASSOC", ``(x+y)+z = x+(y+z)``);
val pax3  = ("MUL_ASSOC", ``(x*y)*z = x*(y*z)``);
val pax14 = ("LE_S",   ``0 < SUC 0``);

val cl   = List.concat (map (find_terms is_const o snd) [pax14,pax1,pax3]);
val cset = mk_fast_set Term.compare cl;
val arity = [2,2,0,2,2,1];
val cal = combine (cset,arity);
val equal = List.nth (cset,4);
val percjl = uniform_term 500 cset (20, ``:num``);

(* Training examples *)
fun mk_one_triple () =
  let 
    val tm1 = hd (shuffle percjl)
    val tm2 = hd (shuffle percjl)
    val eqtm1 = list_mk_comb (equal,[tm1,tm2])
    val eqtm2 = list_mk_comb (equal,[tm2,tm1])
    fun f x = if can DECIDE x then 1.0 else 0.0
    val le12 = list_mk_comb (``$<``,[tm1,tm2])
    val le21 = list_mk_comb (``$<``,[tm2,tm1])
    val poli as [a,b,c] = map f [le12,eqtm1,le21]
    val eval = 0.0 * a + 0.5 * b + 1.0 * c
  in
    if all (fn x => x < 0.5) poli 
    then NONE
    else SOME [(eqtm1,(eval,poli)),(eqtm2,(1.0 - eval, rev poli))]
  end

val trainset = List.concat (List.mapPartial I 
  (parmap 3 mk_one_triple (List.tabulate (10000,fn _=> ()))));
val prepset = prepare_trainset trainset;

(* Treenn *)
val dim = 10;
val poln = 3;
val bsize = 15; 
val epochn = 200; 
val _ = learning_rate := 0.01;

val schedule = [(200,0.01),(200,0.001),(200,0.0001)];

(* show training accuracy and save the graph *)

val _ = writel (tactictoe_dir ^ "/rl/trainset") [string_of_trainset trainset];
val randtreenn = random_treenn dim cal poln;
val trainedtreenn = 
  train_treenn_schedule dim randtreenn bsize prepset schedule;

val _ = writel (tactictoe_dir ^ "/rl/treenn")[string_of_treenn trainedtreenn]
val learnedmap = map_assoc (preevalpoli_tm trainedtreenn) (map fst trainset);
val _ = writel (tactictoe_dir ^ "/rl/learnedmap")
  [string_of_trainset learnedmap];

val tm = ``SUC (SUC (SUC 0)) = SUC 0``;
val result = preevalpoli_tm trainedtreenn tm;

val tm = ``SUC 0 = SUC (SUC (SUC 0))``;
val result = preevalpoli_tm trainedtreenn tm;

val testset = List.concat (List.mapPartial I 
  (parmap 3 mk_one_triple (List.tabulate (1000,fn _=> ()))));

val testedset = map (fn x => (x, preevalpoli_tm trainedtreenn (fst x))) testset

fun maxi l = fst (hd (dict_sort compare_rmax (number_list 0 l)))
fun is_correct ((cj,a),b) = (maxi (snd a) = maxi (snd b));
val correctl = filter is_correct testedset;
val sucrate = percent (int_div (length correctl) (length testedset));



fun baseline tm = 
  let val (a,b) = dest_eq tm in
    case Int.compare (term_size a, term_size b) of
      LESS => (0.0,[1.0,0.0,0.0])  
    | EQUAL => (0.0,[0.0,1.0,0.0])  
    | GREATER => (0.0,[0.0,0.0,1.0])
  end

val testedset = map (fn x => (x, baseline (fst x))) testset;


  val x = “x:num”;
  val th0 = SPEC “0” arithmeticTheory.ADD1;

val thm = ASSUME “(SUC 0 + SUC 1) > SUC 0”;

val newthm = SUBST [x |-> th0] “(x + SUC 1) > SUC 0” thm;

fun occur_in tm stm = length (find_terms (fn x => x = stm) tm); 



load "tttRL"; load "tttSynt"; load "holyHammer";
open tttRL tttTools holyHammer tttSynt tttNN tttNNtree;
val ERR = mk_HOL_ERR "tttRL";
val _ = clean_dir (tactictoe_dir ^ "/rl");

val pax1  = ("ADD_ASSOC", ``(x+y)+z = x+(y+z)``);
val pax3  = ("MUL_ASSOC", ``(x*y)*z = x*(y*z)``);
val pax14 = ("LE_S",   ``0 < SUC 0``);

val cl   = List.concat (map (find_terms is_const o snd) [pax14,pax1,pax3]);
val cset = mk_fast_set Term.compare cl;
val arity = [2,2,0,2,2,1];
val cal = combine (cset,arity);


val percjl = uniform_term 200 cset (10, ``:bool``);
fun decompose x =
  let val (a,b) = (lhand x, rand x) in
    if term_size a < term_size b then (a,b) else (b,a)
  end

val l = map decompose percjl;
fun is_subtm (stm,tm) = can (find_term (fn x => x = stm)) tm;
val (l1,l2) = partition is_subtm l;
val lneg = first_n 1000 (shuffle l2);

fun assoc_pos (a,b) = 
  let 
    val rand_stm = hd (shuffle (find_terms (fn x => type_of x = ``:num``) b)) 
  in
    [(mk_eq (a,b),(0.0,[]:real list)),(mk_eq (rand_stm,b),(1.0,[]))]
  end 
val trainset = List.concat (map assoc_pos lneg);


val percjl = uniform_term 200 cset (10, ``:num``);
val all = cartesian_product percjl percjl;
val all100000 = first_n 100000 (shuffle all);
val (posl,negl) = partition is_subtm all100000;
val negl500 = first_n 500 negl;
fun fp x (a,b) = (mk_eq (a,b),(x:real,[]:real list));
val trainset = map (fp 1.0) posl @ map (fp 0.0) negl500;


val all100000 = first_n 100000 (shuffle all);
val (posl,negl) = partition is_subtm all100000;
val negl500 = first_n 500 negl;
val testset = map (fp 1.0) posl @ map (fp 0.0) negl500;
         
val prepset = prepare_trainset trainset;

(* Treenn *)
val dim = 10;
val poln = 0;
val bsize = 15;
val schedule = [(200,0.01),(200,0.001),(200,0.0001)];

(* show training accuracy and save the graph *)

val _ = writel (tactictoe_dir ^ "/rl/trainset") [string_of_trainset trainset];
val randtreenn = random_treenn dim cal poln;
val trainedtreenn = 
  train_treenn_schedule dim randtreenn bsize prepset schedule;

val _ = writel (tactictoe_dir ^ "/rl/treenn")[string_of_treenn trainedtreenn]
val learnedmap = map_assoc (preevalpoli_tm trainedtreenn) (map fst trainset);
val _ = writel (tactictoe_dir ^ "/rl/learnedmap")
  [string_of_trainset learnedmap];

val test_percjl = uniform_term 200 cset (10, ``:bool``);
val test_l      = map decompose percjl;
val (_,test_l2) = partition is_subtm test_l;
val test_lneg   = first_n 1000 (shuffle test_l2);
val testset = List.concat (map assoc_pos test_lneg);
val testedset = 
  map (fn x => (x, preevalpoli_tm trainedtreenn (fst x))) testset

fun is_correct ((cj,a),b) = 
  if fst a < 0.5 then fst b < 0.5 else fst b >= 0.5
val (correctl,wrongl) = partition is_correct testedset;
val sucrate = percent (int_div (length correctl) (length testedset));

val tm = ``SUC (0 + 0) = 0 + 0 * 0``;


val result = preevalpoli_tm trainedtreenn tm;


(* Todo 
  1) Look at the primitive inference rules. use SUBS_OCCS.
  2) Update the looping management code. (Rescale according to looping priors)
  3) Do a cut-full theorem prover. (small experiment in Peano arithmetic)
  4) 



*)

*)

end (* struct *)
