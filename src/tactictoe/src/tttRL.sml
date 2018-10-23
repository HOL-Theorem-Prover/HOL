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

fun tac_isloop (tree: goal tree) pid pos = case pos of
    (_, NONE) => false
  | (true, _) => false
  | (false, SOME gl) =>
  let 
    val nodel   = map (fn x => dfind x tree) (genealogy pid)
    val p1nodel = filter (fst o #pos) nodel
    val pgl     = map (only_hd o valOf o snd o #pos) p1nodel
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
(* only works if you create only one goal *)
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

(* 
fun preevalpoli treenn pos = case pos of
    (true, SOME [g]) => apply_treenn treenn (list_mk_imp g)
  | _                => raise ERR "preevalpoli1" ""

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
*)

(* Todo 
  1) Look at the primitive inference rules. use SUBS_OCCS.
  2) Update the looping management code. (Rescale according to looping priors)
  3) Do a cut-full theorem prover. (small experiment in Peano arithmetic)
  4) 



*)

end (* struct *)
