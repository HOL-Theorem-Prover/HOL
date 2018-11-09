(* ========================================================================= *)
(* FILE          : tttRobber.sml                                             *)
(* DESCRIPTION   : Theorem prover based on cut introduction                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure tttRobber :> tttRobber =
struct
 
open HolKernel boolLib Abbrev tttTools tttNN tttNNtree tttMCTS tttSynt

val ERR = mk_HOL_ERR "tttRobber"
val dbg = dbg_file "debug_tttRobber"

(* -------------------------------------------------------------------------
   Check if the preimage is in the dictionary of proven thing.
   ------------------------------------------------------------------------- *)

fun find_proof (pdict,antel) =
  let 
    fun g (tm,x) = case x of
       StepSub y =>
         dmem (snd y) pdict andalso dmem (recover_cut tm (fst y)) pdict
     | StepSym ante    => dmem ante pdict
     | StepNegSym ante => dmem ante pdict
     | StepAp ante     => dmem ante pdict
     | StepInj ante    => dmem ante pdict
    fun f (tm,l) = (tm, filter (fn x => g (tm,x)) l)
  in
    map f antel
  end 

fun onestep (pdict,antel) =
  let  
    val pl = filter (fn x => not (null (snd x))) (find_proof (pdict,antel))
    val newpdict = daddset (map fst pl) pdict  
    fun test (x,_) = 
      not (dmem x newpdict) andalso not (dmem (negate x) newpdict)
    val newantel = filter test antel
  in
    (pl,(newpdict,newantel))
  end

fun nstep n acc (pdict,antel) =
  if n <= 0 orelse null antel then rev acc else
  let val (pl,(newpdict,newantel)) = onestep (pdict,antel) in
    nstep (n - 1) (pl :: acc) (newpdict,newantel)
  end

val nstepl = nstep 10 [] (pdict0,ante0);

(* -------------------------------------------------------------------------
   Extract policy examples
   ------------------------------------------------------------------------- *)

fun value_of_step step = case step of
    StepSym _    => 1.0
  | StepNegSym _ => 2.0
  | StepAp _     => 3.0
  | StepInj _    => 4.0
  | StepSub (_,ante) => 5.0 + Real.fromInt (term_size ante)

fun step_choice stepl = 
  let val (step,_) = 
    hd (dict_sort compare_rmin (map_assoc value_of_step stepl)) 
  in
    step
  end

fun poli_of_step step = case step of
    StepSym _    => [1.0,0.0,0.0,0.0,0.0]
  | StepNegSym _ => [0.0,1.0,0.0,0.0,0.0]
  | StepAp _     => [0.0,0.0,1.0,0.0,0.0]
  | StepInj _    => [0.0,0.0,0.0,1.0,0.0]
  | StepSub _    => [0.0,0.0,0.0,0.0,1.0]

(* -------------------------------------------------------------------------
   Choosing the position
   ------------------------------------------------------------------------- *)

fun tag_term tm = 
  let val ty = type_of tm in
    mk_comb (mk_var ("tag_var", mk_type ("fun",[ty,ty])), tm)
  end

fun tag_position (tm,pos) = 
  if null pos then tag_term tm else 
  let 
    val (oper,argl) = strip_comb tm 
    fun f i arg = 
      if i = hd pos
      then tag_position (arg,tl pos)
      else arg
  in
    list_mk_comb (oper, mapi f argl)
  end

fun all_prefix acc l = case l of
    [] => [rev acc]
  | a :: m => rev acc :: all_prefix (a :: acc) m

fun two_arg tm = length (snd (strip_comb tm)) = 2;

fun mk_choice pos = 
  if null pos then NONE else SOME (butlast pos, last pos)

fun sc_descent x = case x of Stop => 0.0 | Continue => 1.0
fun sc_descarg x = case x of Left => 0.0 | Right => 1.0 

fun choice_of_pos (tm,((pos,res),ante)) =
  let 
    val posl = all_prefix [] pos
    val choicel0 = List.mapPartial mk_choice posl
    val descentl = 
      map_assoc (fn _ => Continue) (butlast posl) @ [(last posl, Stop)]
    val nn1 = map_fst (fn x => tag_position (tm,x)) descentl
    fun g (locpos,i) = 
      if two_arg (subtm_at_pos locpos tm)
      then if i = 0 then SOME (locpos,Left) else SOME (locpos,Right)  
      else NONE
    val choicel1 = List.mapPartial g choicel0
    val nn2 = map_fst (fn x => tag_position (tm,x)) choicel1
  in
    (map_snd sc_descent nn1, map_snd sc_descarg nn2) 
  end
    
(* -------------------------------------------------------------------------
   Choosing the residue
   ------------------------------------------------------------------------- *)

fun policy_of_res imit = case imit of
    ImitZero => [1.0,0.0,0.0]
  | ImitSuc  => [0.0,1.0,0.0]
  | ImitAdd  => [0.0,0.0,1.0]

fun choice_of_res (tm,((pos,res),ante)) =
  let
    val tagtm = tag_position (tm,pos)
    val red = subtm_at_pos pos tm
    fun f x = mk_conj (tagtm, mk_eq (red,x))
    val l0 = term_path res
    val l1 = map_snd policy_of_res l0
    val l2 = map_fst f l1
  in
    l2
  end

(* -------------------------------------------------------------------------
   All in one : policy
   ------------------------------------------------------------------------- *)

fun all_in_one nstepl =
  let
    val prepoll0 = List.concat nstepl
    val prepoll1 = map_snd step_choice prepoll0
    (* choosing the tactic *)
    val tacchoice_exl = map_snd poli_of_step prepoll1
    val prepoll3 = 
      mapfilter (fn (tm,step) => (tm, dest_stepsub step)) prepoll1
    (* choosing the position *)
    val (stop_exl, lr_exl) = split (map choice_of_pos prepoll3)
   (* choosing the residue *)
    val reschoice_exl = List.concat (map choice_of_res prepoll3)
  in
    (tacchoice_exl, List.concat stop_exl, List.concat lr_exl, reschoice_exl)
  end

val (tacchoice_exl, stop_exl, lr_exl, reschoice_exl) = all_in_one nstepl;

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

load "tttNNtree"; open tttNNtree;

fun trainset_info trainset =
  let
    val mean = average_real (map snd trainset)
    val dev = standard_deviation (map snd trainset)
  in
    "  length: " ^ int_to_string (length trainset) ^ "\n" ^ 
    "  mean: " ^ Real.toString mean ^ "\n" ^ 
    "  standard deviation: " ^ Real.toString dev
  end

fun wrap_train_treenn (dim,cal) trainset =
  let
    val info     = trainset_info trainset
    val _        = print_endline info
    val bsize    = 16
    val schedule = [(50,0.1),(50,0.01)]
    val prepset  = prepare_trainsetone trainset
    val treenn   = random_treenn dim cal
    val ((treenn,loss), nn_tim) = 
      add_time (train_treenn_schedule dim treenn bsize prepset) schedule
  in
    print_endline ("  NN Time: " ^ Real.toString nn_tim);
    print_endline ("  Last loss: " ^ Real.toString loss);
    treenn
  end

fun fo_terms tm = 
  let val (oper,argl) = strip_comb tm in 
    tm :: List.concat (map fo_terms argl)
  end  

fun operl_of_term tm = 
  let 
    val tml = mk_fast_set Term.compare (fo_terms tm)
    fun f x = let val (oper,argl) = strip_comb x in (oper, length argl) end  
  in
    mk_fast_set (cpl_compare Term.compare Int.compare) (map f tml)
  end

(* -------------------------------------------------------------------------
   Simplest eval.
   to do: figure out how to eval other nodes.
   Maybe initially give a reward of 0.0 for the other nodes.
   ------------------------------------------------------------------------- *)

val tmdist0 = map fst pl0;
val tmdistl = tmdist0 :: map (map fst) nstepl;
val decay = 0.95;

fun mk_eval i l = 
  let val coeff = Math.pow (decay, Real.fromInt i) in
    map (fn x => (x,1.0)) l
  end

val eval_exl1 = List.concat (mapi mk_eval tmdistl);
val eval_exl2 = map (fn (a,b) => (negate a, 0.0)) eval_exl1;
val eval_exl = eval_exl1 @ eval_exl2;

(* Do one-step look ahead for negative there *)
val poseval_pexl = map_snd (fn x => 1.0) stop_exl;
val reseval_pexl = map_snd (fn x => 1.0) reschoice_exl;

(* parameters of treenns *)
val cj   = ``SUC 0 + 0 <> 0`` ;
val cal  = operl_of_term cj;
val cset = mk_fast_set Term.compare (find_terms is_const cj);
val dim  = 10;

(* training *)
val trainset = eval_exl;
val treenn = wrap_train_treenn (dim,cal) trainset;

val sc = eval_treenn treenn ``SUC 0 + SUC 0 = SUC (SUC (SUC 0))``;

val sc = eval_treenn treenn ``0 = 0 + 0``;



(* tac choice step *)
fun apply_tac tac tm = case tac of
    StepSym _    => TacChoice (sym_tac tm)
  | StepNegSym _ => TacChoice (negsym_tac tm)
  | StepAp _     => TacChoice (ap_tac tm)
  | StepInj _    => TacChoice (inj_tac tm)
  | StepSub _    => StopChoice (tm,[])

(* position choice *)
fun descend_pos (tm,pos) stopchoice = case stopchoice of
    Stop     => ResChoice ((tm,pos), startres)
  | Continue => 
    let 
      val subtm = subtm_at_pos pos tm
      val (_,argl) = strip_comb subtm
    in
      case argl of
        []    => ResChoice ((tm,pos), startres)     
      | [a]   => StopChoice (tm, pos @ [0])
      | [a,b] => LrChoice (tm,pos) 
      | _     => raise ERR "descend_pos" " "
    end

fun descend_lr (tm,pos) lrchoice = case lrchoice of
    Left  => StopChoice (tm, pos @ [0])
  | Right => StopChoice (tm, pos @ [1])

(* residue choice *)
fun expand_res ((tm,pos),res) imit = 
  let val newres = apply_imit imit res in
    if is_subtm active_var newres 
    then ResChoice ((tm,pos),newres)
    else TermChoice (sub_at_pos tm (pos,res), recover_cut tm (pos,res))
  end


(* This is the only backward step that can change the player *)


fun altern_player altern player (tm1,tm2) = case altern of
    First     => (not player, TacChoice tm1) 
  | Second    => (not player, TacChoice tm2)
  | NegFirst  => (player, TacChoice (negate tm1))
  | NefSecond => (player, TacChoice (negate tm2))

(* two player : one is trying to prove the other to disprove 
   Think about it without the decay first.
   
   A reward of 0 for the second player means that the term has been disproven
   
   try to instantiate apply_move and status_of
    
  *)

(* -------------------------------------------------------------------------
   Get the policy for player2
   ------------------------------------------------------------------------- *)






end (* struct *)

(* test 
load "tttNNtree"; open tttNNtree;

todo: 
  
  1) human readable  1 = SUC 0

load "holyHammer"; open holyHammer;
val eq1 = ``SUC 0 = 1``;
val eq2 = ``SUC 1 = 2``;
val eq3 = ``SUC 2 = 3``;
val eq4 = ``SUC 3 = 4``;
val eq5 = ``SUC 4 = 5``;
val eql = [eq1,eq2,eq3,eq4,eq5];
fun eq_to_sub eq = [{redex = lhs eq, residue = rhs eq}];
val subl = map eq_to_sub eql;

val tm = ``SUC (SUC 0) + SUC 0 = SUC (SUC (SUC 0))``;

fun human_readable subl tm =
  let fun f (sub,x) = subst sub x in
    foldl f tm subl
  end

val readable = human_readable subl tm;


*)

(*
2) make tactictoe return a theorem.



*)









(* -------------------------------------------------------------------------
   Status
   ------------------------------------------------------------------------- *)

fun is_axiom tm = not (null (match_axiom tm))

fun status_of situation =
  if is_axiom (tm_of_sit situation)
  then Win
  else Undecided

(* -------------------------------------------------------------------------
   Game primitives
   ------------------------------------------------------------------------- *)

(* todo regularization with respect to the size of the terms 
   maybe just hard cut-off for now *)

datatype board = 
  TermChoice of (term * term) | 
  TacChoice  of term |
  StopChoice of (term * int list) |
  LrChoice   of (term * int list) |
  ResChoice  of ((term * int list) * term)

fun p1_startpos cj = (true, TacChoice cj)
fun p2_startpos cj = (false, TacChoice cj)

fun string_of_board x = x

fun string_of_pos x = x

fun board_to_nnterm board = case board of
    TermChoice (tm1,tm2) => mk_conj (tm1,tm2) 
  | TacChoice  tm => tm
  | StopChoice (tm,pos) => tag_position (tm,pos)
  | LrChoice (tm,pos) => tag_position (tm,pos)
  | ResChoice ((tm,pos),res) => 
    let val cut = recover_cut ((tm,pos),res) in 
      mk_conj (tag_position (tm,pos), cut)
    end     

(* 
  eval_treenn with multiple output 
  poli_treenn
*)

(* -------------------------------------------------------------------------
   Policy and evaluation
   ------------------------------------------------------------------------- *)

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

fun fevalpoli (alltnn1,alltnn2) sit =
  if fst sit
  then p1evalpoli alltnn1 pos
  else p2evalpoli alltnn2 pos

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


(* Todo:
  0) refractor TacticToe and HolyHammer code:
  1) remove unnecessary experiments.
  2) isolate evaluation framework in tttTest and hhTest. (like fishtest)
*)

end (* struct *)
