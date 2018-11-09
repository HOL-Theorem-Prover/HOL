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

type alltnn = 
  (tttNNtree.treenn * tttNNtree.treenn *
   tttNNtree.treenn * tttNNtree.treenn)

type allex =  
  ((term * real) list * (term * real) list *
   (term * real) list * (term * real) list)


(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val initcut_glob     = ref T
val build_terms_glob = ref (fn _ => [T])
val axl_glob         = ref []
val termsize_glob   = ref 20

val cutl_glob = ref []
val axl_glob2 = ref []

fun is_provable g = null (fst (REWRITE_TAC (!axl_glob2) g)) 

(* -------------------------------------------------------------------------
   Timers
   ------------------------------------------------------------------------- *)

val fevalpolitime = ref 0.0
val statusoftime  = ref 0.0
val applymovetime = ref 0.0

fun fevalpoli_timer f x  = total_time fevalpolitime f x
fun status_of_timer f x  = total_time statusoftime f x
fun apply_move_timer f x = total_time applymovetime f x

 
fun init_timers () =
  (
  backuptime    := 0.0;
  selecttime    := 0.0;
  fevalpolitime := 0.0;
  statusoftime  := 0.0;
  applymovetime := 0.0
  )

fun string_of_timers tim =
  let 
    val sl = 
      [
      "MCTS time : " ^ Real.toString tim,
      "  backup time     : " ^ Real.toString (!backuptime), 
      "  select time     : " ^ Real.toString (!selecttime), 
      "  fevalpoli time  : " ^ Real.toString (!fevalpolitime), 
      "  status_of time  : " ^ Real.toString (!statusoftime), 
      "  apply_move time : " ^ Real.toString (!applymovetime)
      ]
  in
    String.concatWith "\n" sl
  end

(* -------------------------------------------------------------------------
   Rewriting
   ------------------------------------------------------------------------- *)

fun all_sub axi tm = 
  let 
    val sub    = [{redex = lhs axi, residue = rhs axi}]
    val nb_occ = length (find_terms (fn x => x = lhs axi) tm) 
  in
    List.tabulate (nb_occ, fn i => subst_occs [[i+1]] sub tm)
  end

fun rewrite_with ax tm =
  let 
    val tml = mk_fast_set Term.compare (find_terms (fn _ => true) tm)
    val subl0 = mapfilter (fn x => match_term (lhs ax) x) tml
    val subl1 = fst (split subl0)
    val axil = map (fn x => subst x ax) subl1 
  in
    mk_fast_set Term.compare (List.concat (map (fn x => all_sub x tm) axil))
  end

fun all_rewrite (asm,w) = 
  let 
    val tml0 = List.concat (map (fn x => rewrite_with x w) (!axl_glob))
    val tml1 = mk_fast_set Term.compare tml0
  in
    map (fn x => (asm,x)) tml1
  end

val rewrite_flag = ref false

val rwcut_flag = ref false

(* -------------------------------------------------------------------------
   Game primitives
   ------------------------------------------------------------------------- *)

(* move *)
datatype cutter_move = 
  Forget   of term | 
  InitCut  of term | 
  BuildCut of term | 
  Cut      of term | 
  Rewrite  of goal |
  Rwcut    of goal list |
  Choice   of goal | 
  Changeplayer of goal

fun string_of_move move = case move of
    Forget   tm => "Forget"
  | InitCut  tm => "InitCut"
  | BuildCut tm => "BuildCut"
  | Cut      tm => "Cut"
  | Rewrite  g  => "Rewrite"
  | Rwcut    gl => "Rwcut " ^ String.concatWith " " (map string_of_goal gl)
  | Choice   g  => "Choice"

fun dest_choice x = case x of
  Choice g => g | _ => raise ERR "dest_choice" ""

(* board *)
datatype cutter_board = 
  Prove of goal * term option | 
  Choose of goal list |



fun dest_board1 x = case x of
  Board1 (g,tmo) => (g,tmo) | _ => raise ERR "dest_board1" ""

fun dest_board2 x = case x of
  Board2 gl => gl | _ => raise ERR "dest_board2" ""

fun p1_startpos cj = (true, Board1 (([],cj),NONE))

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

(* fun apply_buildcut (sub,i) (g,cut) = 
  (g, subst_occs [[i+1]] sub cut)
*)

fun apply_cut tm (asl,w) = 
  [(asl,tm), (tm :: filter (fn x => x <> tm) asl, w)] 

fun apply_forget tm (asl,w) = (filter (fn x => x <> tm) asl, w) 

fun p1_apply_move move g = case move of
    Forget tm       => (true, Board1 (apply_forget tm g, NONE))
  | InitCut cut     => (true, Board1 (g, SOME cut))
  | BuildCut newcut => (true, Board1 (g, SOME newcut))
  | Cut cut         => (false, Board2 (apply_cut cut g)) 
  | Rewrite g1      => (true, Board1 (g1, NONE))
  | Rwcut gl        => (false, Board2 gl)
  | _               => raise ERR "p1_apply_move" ""

fun p2_apply_move move gl = (true, Board1 (dest_choice move, NONE))

fun cutter_apply_move move pos = case pos of
    (true, Board1 (g,_)) => p1_apply_move move g
  | (false, Board2 gl)   => p2_apply_move move gl
  | _                    => raise ERR "apply_move" ""


(* -------------------------------------------------------------------------
   Status
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

datatype primitive = Inst | Refl | Subs | Apterm | NotPrimitive

fun string_of_primitive p = case p of
    Inst => "Axiom: inst"  
  | Refl => "Axiom: refl"
  | Subs => "Axiom: subs"
  | Apterm => "Axiom: apterm"
  | NotPrimitive => "Axiom: other"

fun primitive g =
  if exists (fn x => is_inst x g) (!axl_glob) then Inst else
  if is_refl g   then Refl else
  if is_subs g   then Subs else
  if is_apterm g then Apterm else
  NotPrimitive
  
fun is_primitive g = not (primitive g = NotPrimitive)

fun cutter_status_of pos =
  if fst pos andalso is_primitive (fst (dest_board1 (snd pos))) 
  then Win
  else Undecided

(*
  let fun toobig tm = term_size tm > (!termsize_glob) in
    (* if fst pos andalso (toobig (valOf (snd (dest_board1 (snd pos))))
                        handle Option => false)
      then Lose *)
    (* else  
      if (not (fst pos)) andalso 
      exists (not o is_provable) (dest_board2 (snd pos))
      then Lose
      *)
  end
*)

(* -------------------------------------------------------------------------
   Policy and evaluation
   ------------------------------------------------------------------------- *)

val lookup_flag = ref false
val lookup_ref = 
  ref (dempty Term.compare, 
       dempty Term.compare, 
       dempty Term.compare, 
       dempty Term.compare)

(* Player 1 *)

(* evaluation *)
fun p1pos_to_nnterm pos = 
  let val (g,tmo) = dest_board1 (snd pos) in
    case tmo of
      NONE    => goal_to_nnterm g
    | SOME tm => cutpos_to_nnterm (g,tm) 
  end

fun p1eval j1etnn pos = 
  let val nntm = p1pos_to_nnterm pos in
    if !lookup_flag 
    then (dfind nntm (#1 (!lookup_ref)) handle NotFound => 0.5)
    else eval_treenn j1etnn nntm
  end

(* policy *)
fun p1move_to_nnterm (g,tmo) move =
  case move of
    Forget tm   => forget_to_nnterm (g,tm)
  | InitCut tm  => initcut_to_nnterm (g,tm)
  | BuildCut tm => buildcut_to_nnterm ((g,valOf tmo),tm)
  | Cut tm      => cut_to_nnterm (g,tm)
  | Rewrite g1  => goallist_to_nnterm [g,g1]
  | Rwcut gl    => goallist_to_nnterm (g :: gl)
  | _           => raise ERR "p1move_to_nnterm" ""

fun eval_p1move default j1ptnn (g,tmo) move = 
  let val nntm = p1move_to_nnterm (g,tmo) move in
    if !lookup_flag 
    then (dfind nntm (#2 (!lookup_ref)) handle NotFound => default)
    else eval_treenn j1ptnn nntm
  end

fun rewrite_with_cut cut (_,w) =
  map (fn x => Rwcut [([],cut),([],x)]) (all_sub cut w)

fun p1poli j1ptnn pos = case pos of
    (true, Board1 (g, NONE)) =>
    let 
      val movel = 
        if !rewrite_flag 
          then map Rewrite (all_rewrite g)
        else if !rwcut_flag 
          then 
            let  
              val d = count_dict (dempty Term.compare) 
                (find_terms (fn _ => true) (snd g))
              val cutl = filter (fn x => dmem (lhs x) d) (!cutl_glob)
            in
              List.concat (map (fn x => rewrite_with_cut x g) cutl)
            end
        else InitCut (!initcut_glob) :: map Forget (fst g) 
      val default = 1.0 / Real.fromInt (length movel)
    in
      map_assoc (eval_p1move default j1ptnn (g, NONE)) movel
    end
  | (true, Board1 (g, SOME cut)) =>
    let
      val movel = [Cut cut] @ map BuildCut ((!build_terms_glob) cut)
      val default = 1.0 / Real.fromInt (length movel)
    in
      map_assoc (eval_p1move default j1ptnn (g, SOME cut)) movel
    end
  | _ => raise ERR "p1poli" ""  

fun p1evalpoli (j1etnn,j1ptnn) pos = 
  (p1eval j1etnn pos, p1poli j1ptnn pos)

(* Player 2 *)

(* evaluation *)
fun p2pos_to_nnterm pos = goallist_to_nnterm (dest_board2 (snd pos))

fun p2eval j2etnn pos = 
  let val nntm = p2pos_to_nnterm pos in 
    if !lookup_flag 
    then (dfind nntm (#3 (!lookup_ref)) handle NotFound => 0.5)
    else eval_treenn j2etnn nntm
  end

(* policy *)
fun p2move_to_nnterm gl move =
  case move of
    Choice g   => goalchoice_to_nnterm (gl,g)
  | _          => raise ERR "p2move_to_nnterm" ""

fun eval_p2move default j2ptnn gl move =
  let val nntm = p2move_to_nnterm gl move in
    if !lookup_flag 
    then (dfind nntm (#4 (!lookup_ref)) handle NotFound => default)
    else eval_treenn j2ptnn nntm
  end

fun p2evalpoli (j2etnn,j2ptnn) pos =
  let 
    val eval    = p2eval j2etnn pos 
    val gl      = dest_board2 (snd pos)
    val movel   = map Choice gl
    val default = 1.0 / Real.fromInt (length movel)
  in
    (eval, map_assoc (eval_p2move default j2ptnn gl) movel)
  end

(* Player 1 + Player 2 *)
fun cutter_fevalpoli (j1etnn,j1ptnn,j2etnn,j2ptnn) pos =
  if fst pos 
  then p1evalpoli (j1etnn,j1ptnn) pos
  else p2evalpoli (j2etnn,j2ptnn) pos

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
    "  length: " ^ int_to_string (length trainset) ^ "\n" ^ 
    "  mean: " ^ Real.toString mean ^ "\n" ^ 
    "  standard deviation: " ^ Real.toString dev
  end

fun save_trainset name trainset =
  let val info = trainset_info trainset in 
    log info;
    save name (info ^ "\n\n" ^ string_of_trainsetone trainset)
  end

fun wrap_train_treenn (dim,cal) trainset =
  let
    val info     = trainset_info trainset
    val _        = summary info
    val bsize    = 16
    val schedule = [(50,0.1),(50,0.01)]
    val prepset  = prepare_trainsetone trainset
    val treenn   = random_treenn dim cal
    val ((treenn,loss), nn_tim) = 
      add_time (train_treenn_schedule dim treenn bsize prepset) schedule
  in
    summary ("  NN Time: " ^ Real.toString nn_tim);
    summary ("  Last loss: " ^ Real.toString loss);
    treenn
  end

(* -------------------------------------------------------------------------
   MCTS wrapper
   ------------------------------------------------------------------------- *)

fun cutter_mcts (nsim,decay) alltnn target =
  let
    val fevalpoli  = fevalpoli_timer (cutter_fevalpoli alltnn)
    val status_of  = status_of_timer cutter_status_of
    val apply_move = apply_move_timer cutter_apply_move
  in
    (
    starttree_of decay fevalpoli status_of (p1_startpos target),
    fn tree => mcts (nsim,decay) fevalpoli status_of apply_move tree
    )
  end

(* -------------------------------------------------------------------------
   Extracting an example from a node
   ------------------------------------------------------------------------- *)

(* evaluation *)
fun evaluation_example node = case #status node of
    Win  => 1.0
  | Lose => 0.0
  | Undecided => #sum node / (#vis node - 1.0)

fun j1eval_ex node = (p1pos_to_nnterm (#pos node), evaluation_example node)
fun j2eval_ex node = (p2pos_to_nnterm (#pos node), evaluation_example node)

(* policy *)
fun move_of_cid cid pol =
  fst (fst (valOf (List.find (fn x => snd x = cid) pol)))

fun string_of_pol pol = 
  let val movel = map (fst o fst) pol in
    String.concatWith "\n  " (map string_of_move movel) 
  end


fun j1poli_ex tree id =
  let 
    val cidscl = policy_example tree id
    val node = dfind id tree
    val (g,tmo) = dest_board1 (snd (#pos node))
    val pol = #pol node
    fun f cid = p1move_to_nnterm (g,tmo) (move_of_cid cid pol)
  in
    if length cidscl <= 1 then [] else map_fst f cidscl
  end

fun j2poli_ex tree id =
  let 
    val cidscl = policy_example tree id
    val node = dfind id tree
    val gl = dest_board2 (snd (#pos node))
    val pol = #pol node
    fun f cid = p2move_to_nnterm gl (move_of_cid cid pol)
  in
    if length cidscl <= 1 then [] else map_fst f cidscl
  end

(* -------------------------------------------------------------------------
   Running partial proofs to collect examples
   ------------------------------------------------------------------------- *)

val partialwin_flag = ref false
val win_flag = ref false

fun collect_exl depth bigsteps (j1e,j1p,j2e,j2p) prover starttree =
  let 
    val tree = prover starttree
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
      then (j1eval_ex root :: j1e, j1poli_ex tree [0] @ j1p, j2e, j2p)
      else (j1e, j1p, j2eval_ex root :: j2e, j2poli_ex tree [0] @ j2p)
  in
    if depth >= bigsteps
      then (log ("  reached maxdepth " ^ int_to_string depth); exl) 
    else 
      case select_bigstep tree [0] of
        NONE => exl
      | SOME cid => 
        let 
          val pol  = #pol (dfind [0] tree)
          val _    = log ("  " ^ string_of_pol pol)
          val move = move_of_cid cid pol
          val _ = log ("    " ^ string_of_move move)
          val newstarttree = cut_tree tree cid 
        in
          collect_exl (depth + 1) bigsteps exl prover newstarttree
        end
  end

fun combine_4 l = case l of
    [] => ([],[],[],[])
  | (a,b,c,d) :: m => 
    let val (am,bm,cm,dm) = combine_4 m in
      (a @ am, b @ bm, c @ cm, d @ dm)
    end
  
fun list_collect_exl (nsim,decay) bigsteps (alltnn,alldict) targetl =
  let 
    val (partialwin,win,ended) = (ref 0,ref 0,ref 0)
    fun f i target =
    let
      val _  = (partialwin_flag := false; win_flag := false)
      val _  = log ("\nTarget " ^ int_to_string i)  
      val (starttree,prover) = cutter_mcts (nsim,decay) alltnn target
      val exl = collect_exl 0 bigsteps ([],[],[],[]) prover starttree
      val _ = 
        if !win_flag orelse !partialwin_flag then incr partialwin else ()
      val _ = if !win_flag then incr win else ()
    in
      exl
    end
    val r = mapi f targetl
    val _ = summary ("  Wins : " ^ (int_to_string (!win)))
    val _ = summary ("  Partial wins : " ^ (int_to_string (!partialwin)))
  in
    combine_4 r
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_loop (ngen,tot) (nsim,decay,bigsteps) targetl (dim,cal) 
  (alltnn,allex) =
  let
    val its   = int_to_string
    val ngens = its ngen
    val _     = summary ("\n\nGeneration: " ^ ngens)
    val _     = summary ("MCTS games")
    val _     = init_timers ()
    val (j1eo,j1po,j2eo,j2po) = allex
    val alldict = 
      (dnew Term.compare (rev j1eo), dnew Term.compare (rev j1po),
       dnew Term.compare (rev j2eo), dnew Term.compare (rev j2po))
    val _ = summary ("Dictionnary lengths")
    val _ = summary ("  " ^ int_to_string (dlength (#1 alldict)))
    val _ = summary ("  " ^ int_to_string (dlength (#2 alldict)))
    val _ = summary ("  " ^ int_to_string (dlength (#3 alldict)))
    val _ = summary ("  " ^ int_to_string (dlength (#4 alldict)))
    val _ = lookup_ref := alldict
    val ((j1e,j1p,j2e,j2p), mcts_tim) = 
      add_time 
      (list_collect_exl (nsim,decay) bigsteps (alltnn,alldict)) targetl
    val _ = summary (string_of_timers mcts_tim)
    val newallex = (j1e @ j1eo, j1p @ j1po, j2e @ j2eo, j2p @ j2po)
  in
    if ngen >= tot 
      then (alltnn, allex) else
    if !lookup_flag 
      then rl_loop (ngen + 1,tot) (nsim,decay,bigsteps) targetl
            (dim,cal) (alltnn,newallex)
    else
      let
        val _      = summary "Training player 1 eval"
        val j1etnn = wrap_train_treenn (dim,cal) (#1 newallex)
        val _      = summary "Training player 1 poli"
        val j1ptnn = wrap_train_treenn (dim,cal) (#2 newallex)
        val _      = summary "Training player 2 eval"
        val j2etnn = wrap_train_treenn (dim,cal) (#3 newallex)
        val _      = summary "Training player 2 poli"
        val j2ptnn = wrap_train_treenn (dim,cal) (#4 newallex)
        val newalltnn = (j1etnn,j1ptnn,j2etnn,j2ptnn)
      in
        rl_loop (ngen + 1,tot) (nsim,decay,bigsteps) targetl
        (dim,cal) (newalltnn,newallex)
      end
  end

fun rl_gen tot (nsim,decay,bigsteps) targetl (dim,cal) =
  let 
    val _ = summary ("Global parameters")
    val _ = summary ("  NN dimension: " ^ int_to_string dim)
    val _ = summary ("  MCTS simulation: " ^ int_to_string nsim)
    val _ = summary ("  MCTS decay: " ^ Real.toString decay)
    val _ = summary ("  MCTS bigsteps: " ^ int_to_string bigsteps)
    val alltnn = 
      (random_treenn dim cal, random_treenn dim cal,
       random_treenn dim cal, random_treenn dim cal)
    val allex = ([],[],[],[])
  in
    rl_loop (0,tot) (nsim,decay,bigsteps) targetl (dim,cal) 
    (alltnn,allex)
  end


(* Example

  load "tttCutter";
  open tttTools tttMCTS tttCutter tttNNtree tttSynt;
  
  erase_log ();
  val _    = initcut_glob := ``0=0``;  

  fun add0l tm  = list_mk_comb (``$+``,[``0``,tm]);
  fun add0r tm  = list_mk_comb (``$+``,[tm,``0``]);
  fun addS tm   = mk_comb (``SUC``,tm);
  fun mult0l tm = list_mk_comb (``$*``,[``0``,tm]);
  fun mult0r tm = list_mk_comb (``$*``,[tm,``0``]);

  val _ = build_terms_glob := build_terms;

  (* parameters of treenns *)
  val cj   = ``(SUC 0) + (SUC 0) = (SUC (SUC 0))`` ;
  val cal  = operl_of_term cj;
  val cset = mk_fast_set Term.compare (find_terms is_const cj);
  val dim  = 10;

  (* Search parameters *)
  val (nsim,decay,bigsteps) = (1600,0.95,20);

  (* Axioms *)
  val ax4 = ``x + 0 = x``;
  val ax4s = ``0 + x = x``;
  val ax5 = ``x + SUC y = SUC (x + y)``;
  val ax5s = ``SUC (x + y) = x + SUC y``;
  val _ = axl_glob := [ax4,ax4s,ax5,ax5s];
  val _ = axl_glob2 := map (fn x => mk_thm ([],x)) [ax4,ax5];  

  (* Targets *)


  (* Addition up to 9 *)
  fun number_n n = 
    if n <= 0 then ``0`` else addS (number_n (n-1));
  val l1 = List.tabulate (4,I);
  val l2 = cartesian_product l1 l1;
  fun addthm (a,b) = 
    let val (tm1,tm2,tm3) = (number_n a, number_n b, number_n (a+b)) in
      mk_eq (list_mk_comb (``$+``,[tm1,tm2]), tm3)
    end
  val targetl = map addthm l2;  
  
  (* Cuts *)
  fun filterf l = first_n 1000000 (shuffle l);
  val cutl = synthetize filterf (1000000,20) cset;
  fun is_provable g = null (fst (REWRITE_TAC (!axl_glob2) g));
  fun mk_goal tm = ([],tm): goal;
  fun is_refl w = 
     is_eq w andalso (let val (a,b) = dest_eq w in a = b end);
  fun is_reducing tm = term_size (lhs tm) >= term_size (rhs tm)

  val validcutl1 = filter (is_provable o mk_goal) cutl;
  val validcutl2 = filter (not o is_refl) validcutl1;
  val validcutl3 = filter (is_reducing) validcutl2;
  val _ = cutl_glob := validcutl3;

  (* Main *)
  (* val _ = lookup_flag := true; *)
  val _ = rwcut_flag := true;
  val _ = termsize_glob := 18;
  val _ = dbg_flag := true;
  val (alltnn,allex) = rl_gen 5 (nsim,decay,bigsteps) targetl (dim,cal);
  
*)

(* todo
  1) tablebase examples. 

     The second player can choose to prove the negation if
     instead of giving back the goal to the first player. 
     ((first/second) are interchangeable)

     Prove A
       
     If I am 90 percent confident I can prove ~A it means
     
     the percentage of chance of proving A is 0.1 * exploration

     P1: Prove B /\ Prove C     
   
              P2 move

     P1: Prove B  P1: Prove C     P2: Prove ~B  P2: prove ~C
           
     There was never a player 2 state.

 

     Something could have some probability of being true or false,
     before it has some probability of being provable.

  2) try to prove that 
     !x y. x+y = y+x
     using induction
                                (minimize (a,c), maximize (b,d))
                                 
          DECIDE (SUC 0 = SUC 0 + SUC 0)  (0.3)
                     
     SUC 0 <> SUC 0 + SUC 0 (0.1) \/ SUC 0 = SUC 0 + SUC 0 (0.3)
   
  

   SUC 0 <> SUC (SUC 0 + 0)  /\  SUC 0 + SUC 0 = SUC (SUC 0 + 0) 
           

  \/ Choose the easiest part
  
  /\ Choose the hardest part


Player 2 could start the game and choose either to prove the negation or to
give back the hand to player 1.


    Add the possibility to do first-order logic.
    And higher-order logic.


*)


(* todo later
  1) Only learns from wins or losses?
  2) see if the distribution of a test run is close to the
     original distribution to detect when the network breaks.
  3) (tentative) split the poli1 player into many parts 
     (forget_asm, build_cut, select_cut)
  4) only select the trained networks if it is better: 
     -- higher number of wins
     -- cross-plays partial wins (or very partial wins)
       (player1 vs competitor player2 and player2 vs competitor player1)  

  6) Have a generator that will generate problems 
     with 50 percent chance of winning (ending in a win)
  7) Tell which move has been applied
     Say by which primitive rules the proof ended.
  8) Allows the first player to Lose.
  9) Add successors
  10) Add multiplication

  11) General algorithm for formula synthesis in higher order logic.
    x: bool ->
  
*)

end (* struct *)
