(* ========================================================================= *)
(* FILE          : tttCutter.sml                                             *)
(* DESCRIPTION   : Theorem prover based on cut introduction                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure tttCutter :> tttCutter =
struct
 
open HolKernel boolLib Abbrev tttTools tttNN tttNNtree tttMCTS tttSynt

val ERR = mk_HOL_ERR "tttCutter"
val dbg = dbg_file "tttCutter"

fun save file s = writel (tactictoe_dir ^ "/exp/" ^ file) [s]

(* Tools *)
fun dset cmp l = dnew cmp (map (fn x => (x,())) l)
fun has_boolty x = type_of x = bool

(* -------------------------------------------------------------------------
   Timers
   ------------------------------------------------------------------------- *)

val fevalpolitime = ref 0.0
val statusoftime  = ref 0.0
val applymovetime = ref 0.0
val synttime      = ref 0.0

fun fevalpoli_timer f x  = total_time fevalpolitime f x
fun status_of_timer f x  = total_time statusoftime f x
fun apply_move_timer f x = total_time applymovetime f x
fun synt_timer f x       = total_time synttime f x
 
fun init_timers () =
  (
  backuptime    := 0.0;
  selecttime    := 0.0;
  fevalpolitime := 0.0;
  statusoftime  := 0.0;
  applymovetime := 0.0;
  synttime      := 0.0
  )

fun string_of_timers tim =
  let 
    val sl = 
      [
      "total time      : " ^ Real.toString tim,
      "backup time     : " ^ Real.toString (!backuptime), 
      "select time     : " ^ Real.toString (!selecttime), 
      "synt time       : " ^ Real.toString (!synttime), 
      "fevalpoli time  : " ^ Real.toString (!fevalpolitime), 
      "status_of time  : " ^ Real.toString (!statusoftime), 
      "apply_move time : " ^ Real.toString (!applymovetime)
      ]
  in
    String.concatWith "\n" sl
  end

(* -------------------------------------------------------------------------
   Game primitives
   ------------------------------------------------------------------------- *)

(* move *)
datatype cutter_move = 
  Forget of term | Cut | InitCut of term | BuildCut of int | Choice of goal 

fun dest_forget x = case x of
  Forget tm => tm | _ => raise ERR "dest_forget" ""

fun dest_choice x = case x of
  Choice g => g | _ => raise ERR "dest_choice" ""

fun dest_buildcut x = case x of
  BuildCut i => i | _ => raise ERR "dest_buildcut" ""

(* board *)
datatype cutter_board = 
  Board1 of goal * term option | Board2 of goal list

fun dest_board1 x = case x of
  Board1 (g,_) => g | _ => raise ERR "dest_board1" ""

fun dest_board2 x = case x of
  Board2 gl => gl | _ => raise ERR "dest_board2" ""

(* starting position *)
fun p1_startpos cj = (true, Board1 ([],cj))

(* -------------------------------------------------------------------------
   Log
   ------------------------------------------------------------------------- *)

fun string_of_pos pos = case pos of
    (true, Board1 (g, SOME tm)) => 
    string_of_goal g ^ " # " ^ term_to_string tm
  | (true, Board1 (g, NONE))    => string_of_goal g 
  | (false, Board2 gl) => 
    String.concatWith " || " (map string_of_goal gl)
  | _ => raise ERR "string_of_pos" ""

(* -------------------------------------------------------------------------
   Move application
   ------------------------------------------------------------------------- *)

fun apply_buildcut (sub,i) (g,cut) = 
  (g, subst_occs [[i+1]] sub cut)

fun apply_cut tm (asl,w) = [(asl,tm), (tm :: asl, w)] 

fun apply_forget tm (asl,w) = (filter (fn x => x <> tm) asl, w) 

fun p1some_apply_move move (g,cut) = case move of
    Cut              => (false, Board2 (apply_cut cut g)) 
  | Buildcut (sub,i) => (true, Board1 (apply_forget tm g, SOME))
  | _                => raise ERR "p1some_apply_move" ""

fun p1none_apply_move move g = case move of
    Forget tm   => (true, Board1 (apply_forget tm g, NONE))
  | InitCut cut => (true, Board1 (apply_forget tm g, SOME cut))
  | _           => raise ERR "p1none_apply_move" ""

fun p2_apply_move move gl = (true, Board1 (dest_choice move))

fun cutter_apply_move move pos = case pos of
    (true, Board1 (g, SOME cut)) => p1some_apply_move move (g,cut)
  | (true, Board1 (g, NONE))     => p1none_apply_move move g
  | (false, Board2 gl)           => p2_apply_move move gl
  | _                            => raise ERR "apply_move" ""

(* -------------------------------------------------------------------------
   Policy and evaluation
   ------------------------------------------------------------------------- *)

fun singleton a = [a]
val goal_of_p1pos  = dest_board1 o snd
fun goal_of_p1node (node:(cutter_board,cutter_move) node) = 
  node |> #pos |> goal_of_p1pos

(* Player 1 *)
fun p1eval j1etnn pos =
  eval_treenn j1etnn (goal_to_nnterm (goal_of_p1pos pos))

(* move generation *)
fun mk_cutl cset =
  let fun filterf tml = first_n 10 (shuffle tml) in
    synt_timer (synthetize filterf (5,20)) cset
  end

fun mk_forgetl acc (asm,w) = case asm of
    []     => []
  | a :: m => (acc @ m,w) :: mk_forgetl (acc @ [a]) (m,w) 

(* move evaluation *)
fun eval_p1move g j1ptnn move =
  let val tm = gt_to_nnterm (g, p1move_to_nnterm move) in
    eval_treenn j1ptnn tm
  end

(* policy *)
fun p1poli cset j1ptnn pos =
  let
    val g = goal_of_p1pos pos
    val movel = map Forget (mk_forgetl [] g) @ map Cut (mk_cutl cset)
  in
    map_assoc (eval_p1move g j1ptnn) movel
  end

fun p1evalpoli cset (j1etnn,j1ptnn) pos =
  (p1eval j1etnn pos, p1poli cset j1ptnn pos)

(* Player 2 *)
fun p2evalpoli (j2etnn,j2ptnn) pos =
  let  
    val gl   = pos |> snd |> dest_board2 
    val tm   = goallist_to_nnterm gl
    val eval = eval_treenn j2etnn tm
    val polisc = eval_treenn j2ptnn tm
    val (g1,g2) = pair_of_list gl
    val poli = [(Choice g1,polisc), (Choice g2, 1.0 - polisc)]
  in
    (eval, poli)
  end

(* Player 1 + Player 2 *)
fun cutter_fevalpoli cset ((j1etnn,j1ptnn),(j2etnn,j2ptnn)) pos =
  if fst pos 
  then p1evalpoli cset (j1etnn,j1ptnn) pos
  else p2evalpoli (j2etnn,j2ptnn) pos

(* -------------------------------------------------------------------------
   Status (end of the game)
   ------------------------------------------------------------------------- *)

fun is_refl (_,w) = is_eq w andalso (let val (a,b) = dest_eq w in a = b end)

fun is_inst tm (_,w) = can (match_term tm) w

fun is_subs_aux (tm1,tm2) tm3 =
  let
    val sub = [{redex = lhs tm1, residue = rhs tm1}]
    val occl  = find_terms (fn x => x = lhs tm1) tm2
    fun f i _ = subst_occs [[i+1]] sub tm2
  in
    mem tm3 (mapi f occl)
  end
  handle _ => raise ERR "is_subs_aux" ""

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

fun cutter_status_of axl pos =
  if fst pos andalso is_primitive axl (dest_board1 (snd pos)) 
  then Win
  else Undecided

(*
fun string_of_wintree i tree wintree =
  let
    fun string_of_id id = String.concatWith "." (map int_to_string (rev id))
    fun f id = 
      string_of_id id ^ ": " ^ string_of_pos (#pos (dfind id tree))
  in
    case wintree of
      Wleaf id     => f id
    | Wnode (id,l) => f id ^ "\n" ^
      String.concatWith "\n" (map (string_of_wintree (i+2) tree) l)
  end
*)

(*
fun is_nodewin node = #status node = Win

fun is_treewin (tree : (cutter_board, cutter_move) tree) = 
  is_nodewin (dfind [0] tree)

fun success_rate l =
  let val winl = map fst (filter (is_treewin o snd) l) in
    length winl
  end
*)


(* -------------------------------------------------------------------------
   Training wrapper
   ------------------------------------------------------------------------- *)

fun merge_trainset trainset1 trainset2 =
  let 
    val trainsetd2 = dnew Term.compare trainset2
    fun overwritten (cj,_) = dmem cj trainsetd2
    val newtrainset1 = filter (not o overwritten) trainset1
  in
    newtrainset1 @ trainset2
  end

fun trainset_info trainset =
  let
    val mean = average_real (map snd trainset)
    val dev = standard_deviation (map snd trainset)
  in
    "length: " ^ int_to_string (length trainset) ^ "\n" ^ 
    "mean: " ^ Real.toString mean ^ "\n" ^ 
    "standard deviation: " ^ Real.toString dev
  end

fun save_trainset name trainset =
  let val info = trainset_info trainset in 
    log info;
    save name (info ^ "\n\n" ^ string_of_trainsetone trainset)
  end

fun wrap_train_treenn (dim,cal) trainset =
  let
    val bsize    = 8
    val schedule = [(200,0.1),(200,0.01),(200,0.001)]
    val prepset  = prepare_trainsetone trainset
    val treenn   = random_treenn dim cal
  in
    train_treenn_schedule dim treenn bsize prepset schedule
  end

fun wrap_train_head opdict dim trainset =
  let
    fun f (a,b) = 
      (add_bias (embed_cache opdict a), 
       norm_vect (Vector.fromList [b]))
    val prepset    = map f trainset
    val headnn     = random_headnn dim
    val nepoch     = 200
    val batchsize  = 16
  in
    learning_rate := 0.05;
    train_nn_nepoch nepoch headnn batchsize prepset
  end

(* -------------------------------------------------------------------------
   MCTS wrapper
   ------------------------------------------------------------------------- *)

(*
fun print_info ngen (tree,tim) =
  let
    val timerinfo = string_of_timers tim
    val status = #status (dfind [0] tree)
    val _ = log ("  " ^ string_of_status status)
    val proof_file = 
      "exp/proof/gen" ^ int_to_string ngen ^ "/" ^ int_to_string i
    val wintrees = if not (status = Win) then "NoProof" else
      let val wintree = winning_tree tree [0] in 
        "Proof" ^ "\n" ^ string_of_wintree 0 tree wintree
      end
  in
    writel_path tactictoe_dir proof_file [timerinfo ^ "\n\n" ^ wintrees]
  end
*)

fun cutter_mcts (nsim,decay) cset alltnn axl startpos =
  let
    val _ = init_timers ()
    val fevalpoli  = fevalpoli_timer (cutter_fevalpoli cset alltnn)
    val status_of  = status_of_timer (cutter_status_of axl)
    val apply_move = apply_move_timer cutter_apply_move
  in
    mcts (nsim,decay) fevalpoli status_of apply_move startpos
  end

(* -------------------------------------------------------------------------
   Helpers for example generation
   ------------------------------------------------------------------------- *)

fun move_visits tree cid =
  #vis (dfind cid tree) handle NotFound => 0.0

fun move_win tree cid =
  #status (dfind cid tree) = Win handle NotFound => false

fun poli_win tree poli = 
  map (fn ((move,_),cid) => (move, move_win tree cid)) poli

fun bool_to_real b = if b then 1.0 else 0.0

(* -------------------------------------------------------------------------
   Extracting an example from a node
   ------------------------------------------------------------------------- *)

fun j1eval_ex node = 
  let val sc =
    if #status node = Win then 1.0 else #sum node / (#vis node - 1.0)
  in
    (goal_to_nnterm (dest_board1 (snd (#pos node))), sc)
  end

fun j2eval_ex node = 
  let val sc =
    if #status node = Win then 1.0 else #sum node / (#vis node - 1.0)
  in
    (goallist_to_nnterm (dest_board2 (snd (#pos node))), sc)
  end

fun j1poli_ex tree node =
  let 
    val vtot = #vis node - 1.0
    val g = dest_board1 (snd (#pos node))
    val poli = #pol node
    val poliwin = poli_win tree poli
    fun mk_term (g,move)  = gt_to_nnterm (g, p1move_to_nnterm move)
    fun winex (move,b)    = (mk_term (g,move), bool_to_real b)
    fun ex ((move,_),cid) = (mk_term (g,move), move_visits tree cid / vtot)
  in
    if exists snd poliwin 
    then map winex poliwin 
    else map ex poli
  end

fun j2poli_ex tree node =
  let 
    val vtot  = #vis node - 1.0
    val gl    = dest_board2 (snd (#pos node))
    val (a,b) = pair_of_list (#pol node)
    val sc    = 
      if move_win tree (snd a) andalso move_win tree (snd a) 
        then (move_visits tree (snd a) / vtot)
      else if move_win tree (snd a) 
        then 0.0 
      else if move_win tree (snd b) 
        then 1.0 
      else (move_visits tree (snd a) / vtot)
  in
    (goallist_to_nnterm gl, sc) 
  end

(* -------------------------------------------------------------------------
   Running partial proofs to collect examples
   ------------------------------------------------------------------------- *)

val partialwin_flag = ref false
val win_flag = ref false
val ended_flag = ref false

fun collect_exl depth maxdepth (j1e,j1p,j2e,j2p) prover startpos =
  let 
    val tree = prover startpos
    val root = dfind [0] tree  
    val reps = 
       if #status root = Win andalso depth = 0
         then 
         (win_flag := true; "  (Win) " ^ string_of_pos (#pos root))
       else if #status root = Win 
         then 
         (partialwin_flag := true; "  (win) " ^ string_of_pos (#pos root))
       else "  " ^ string_of_pos (#pos root)
    val _   = log reps
    val exl = 
      if fst (#pos root)
      then (j1eval_ex root :: j1e, j1poli_ex tree root @ j1p, j2e, j2p)
      else (j1e, j1p, j2eval_ex root :: j2e, j2poli_ex tree root :: j2p)
  in
    if depth >= maxdepth 
      then (log ("  reached maxdepth " ^ int_to_string depth); exl) 
    else 
      case proba_child tree [0] of
        NONE => (ended_flag := true; exl)
      | SOME cid => 
        let val newstartpos = #pos (dfind cid tree) in
          collect_exl (depth + 1) maxdepth exl prover newstartpos
        end
  end

fun list_collect_exl (nsim,decay) maxdepth cset alltnn axl targetl =
  let 
    val (partialwin,win,ended) = (ref 0,ref 0,ref 0)
    fun f i target =
    let
      val _  = 
        (partialwin_flag := false; win_flag := false; ended_flag := false)
      val _  = summary ("Target " ^ int_to_string i)  
      val startpos = p1_startpos target
      fun prover pos = cutter_mcts (nsim,decay) cset alltnn axl pos
      val exl = collect_exl 0 maxdepth ([],[],[],[]) prover startpos
      val _ = if !win_flag orelse !partialwin_flag 
              then incr partialwin
              else ()
      val _ = if !win_flag then incr win else ()
      val _ = if !ended_flag then incr ended else ()
    in
      exl
    end
    val r = mapi f targetl
    val _ = summary ("Ended : " ^ (int_to_string (!ended)))
    val _ = summary ("Wins : " ^ (int_to_string (!win)))
    val _ = summary ("Partial wins : " ^ (int_to_string (!partialwin)))
  in
    r
  end

(* Example

  load "tttCutter"; 
  open tttTools tttMCTS tttCutter tttNNtree tttSynt;
  
  erase_log ();
  (* signature *)
  val cj   = ``0 = 0 + 0`` ;

  val cal  = operl_of_nnterm cj;
  val cset = mk_fast_set Term.compare (find_terms is_const cj);

  (* starting nn *)
  val dim = 10;
  val alltnn = 
    ((random_treenn dim cal, random_treenn dim cal),
     (random_treenn dim cal, random_treenn dim cal));

  (* MCTS parameters *)  
  val decay = 0.99;
  val nsim = 1600;
  val maxdepth = 10;

  (* Axioms *)
  val ax4 = ("ADD_0", ``x + 0 = x``);
  val ax5 = ("ADD_S", ``x + SUC y = SUC (x + y)``);
  val axl = map snd [ax4];

  (* Targets *)
  fun filterf l = first_n 1000 (shuffle l);
  val targetl = synthetize filterf (50,20) cset;

  (* Examples *)
  val exl = list_collect_exl (nsim,decay) maxdepth cset alltnn axl targetl;

  fun combine_4 l = case l of
      [] => ([],[],[],[])
    | (a,b,c,d) :: m => 
      let val (am,bm,cm,dm) = combine_4 m in
        (a @ am, b @ bm, c @ cm, d @ dm)
      end
  
  val (j1e,j1p,j2e,j2p) = combine_4 exl;

  val j1etnn = wrap_train_treenn (dim,cal) j1e;
  val j1ptnn = wrap_train_treenn (dim,cal) j1p;
  val j2etnn = wrap_train_treenn (dim,cal) j2e;
  val j2ptnn = wrap_train_treenn (dim,cal) j2p;

  val alltnn2 = ((j1etnn,j1ptnn),(j2etnn,j2ptnn));
  
  val exl2 = list_collect_exl (nsim,decay) maxdepth cset alltnn2 axl targetl;

  (* todo 
    1) calculate maximum depth from wintree.
    2) include term construction as part of the search space.  (part of the policy of the first player (substitution of 0 by 0+0 starting with 0=0)
    3) do rl loop for 10 loops 
   *)


*)






(* avoiding duplicates (takes the first node) 
fun ln_duplicate (g,(x,best)) = 
  let val n = Real.floor (Math.ln (1.0 + x / cutoff) + 1.0) in
    duplicate n [(g,best)]
  end
fun no_duplicate (g,(x,best)) = duplicate 1 [(g,best)]
fun 
      val d     = dregroup Term.compare l1
    val l2    = map_snd max_score (dlist d)
    val l3    = List.concat (map no_duplicate l2)
fun max_score l =
  let val (a,b) = split l in 
    (sum_real a, (last (dict_sort Real.compare b))) 
  end
fun subterms_of tm = find_terms (fn _ => true) tm
*)

(*
fun p1cut_one threshold (cset,casterl) gentnn input =
  let
    fun evalf tm    = relative_eval gentnn casterl input tm
    fun filterf tml = evalf_to_filterf threshold evalf tml
  in
    synthetize filterf (5,20) cset
  end
*)

(* hacky function that guarantees the policy is not empty 
fun p1cut (cset,casterl) gentnn input =
  let
    fun loop pl l = case l of 
       [] => pl
     | a :: m => 
      let val result = p1cut_one a (cset,casterl) gentnn input in 
        if length result < 2 then loop result m else result
      end
  in
    loop [] [ ~1.0]
  end
*)

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)



(*
fun rl_loop ngen tot cset axl targetl (dim,cal) alltnn allex =
  let
    val its   = int_to_string
    val ngens = its ngen
    val _     = log ("Generation: " ^ ngens)
    val cjpl  = 
      cutter_mcts_list ngen 1600 cset (jtnn,gtnn) axl targetl
    val nthm  = success_rate cjpl
    val _     = summary ("success rate " ^ its ngen ^ ": " ^ its nthm)
  in
    if ngen >= tot then (opdict,jhead,ghead) else
    let
      val _        = log "Training the judge"
      val jtrain   = prepare_judgetnn_data cjpl
      val _        = save_trainset ("jtrain" ^ ngens) jtrain
      val jtrainm  = merge_trainset oldjm jtrain
      val _        = log (trainset_info jtrainm)
      val newjhead = wrap_train_head opdict dim jtrainm
      val newjtnn  = (opdict,newjhead)
      val jvalid   = map_assoc (eval_treenn newjtnn) (map fst jtrain)
      val _        = save_trainset ("jvalid" ^ ngens) jvalid
      val _        = log "Training the generator"
      val gtrain   = prepare_gentnn_data casterl cjpl
      val _        = save_trainset ("gtrain" ^ ngens) gtrain
      val gtrainm  = merge_trainset oldgm gtrain
      val _        = log (trainset_info gtrainm) 
      val newghead = wrap_train_head opdict dim gtrainm
      val newgtnn  = (opdict,newghead)
      val gvalid   = map_assoc (eval_treenn newgtnn) (map fst gtrain)
      val _        = save_trainset ("gvalid" ^ ngens) gvalid
    in
      rl_loop (ngen + 1) tot (cset,casterl) axl targetl (dim,cal) 
        (opdict,newjhead,newghead) (jtrainm,gtrainm)
    end
  end

fun rl_gen tot (cset,casterl) axl targetl (dim,cal) (opdict,jhead,ghead) =
  let 
    val _ = erase_log () 
    val _ = log ("NN dimension: " ^ int_to_string dim) 
  in
    rl_loop 0 tot (cset,casterl) axl targetl (dim,cal) (opdict,jhead,ghead)
    ([],[])
  end
*)


end (* struct *)
