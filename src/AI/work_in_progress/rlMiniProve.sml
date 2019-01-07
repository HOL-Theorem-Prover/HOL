(* ========================================================================= *)
(* FILE          : rlMiniProve.sml                                           *)
(* DESCRIPTION   : Datatypes for the robber theorem prover                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlMiniProve :> rlMiniProve =
struct

open HolKernel Abbrev boolLib aiLib
  mlTreeNeuralNetwork psMCTS rlLib rlMiniRules rlMiniTrain

val ERR = mk_HOL_ERR "rlMiniProve"
val eval_dir = HOLDIR ^ "/src/AI/work_in_progress/eval"
fun log_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end
fun summary s = log_eval "rlMiniProve_knn" s

(* -------------------------------------------------------------------------
   Status
   ------------------------------------------------------------------------- *)

fun p1_startpos target = (true, LrBoard (target,[]))

type situation = bool * board

fun status_of sit = case sit of
    (true, LrBoard (tm,[])) =>
    if tm = F orelse term_size (rhs tm) > 10 orelse term_size (lhs tm) > 10
    then Lose
    else if is_refl tm then Win else Undecided
  | _ => Undecided

(* -------------------------------------------------------------------------
   Evaluation/Policy
   ------------------------------------------------------------------------- *)

fun mk_tnn_fep alltnn sit =
  let val tminput = nntm_of_sit sit in
    case sit of
      (true, LrBoard (tm,pos)) =>
      (eval_treenn (#lreval alltnn) tminput,
       combine (map LrMove all_lrchoice,
                poli_treenn (#lrpoli alltnn) tminput))
    | (true, StopBoard (tm,pos)) =>
      (eval_treenn (#stopeval alltnn) tminput,
       combine (map StopMove all_stopchoice,
                poli_treenn (#stoppoli alltnn) tminput))
    | (true, SubBoard (tm,pos)) =>
      (eval_treenn (#subeval alltnn) tminput,
       combine (map SubMove all_subchoice,
                poli_treenn (#subpoli alltnn) tminput))

    | _ => raise ERR "mk_tnn_fep" ""
  end

fun mk_knn_fep allknn sit =
  let val tminput = nntm_of_sit sit in
    case sit of
      (true, LrBoard (tm,pos)) =>
      (infer_knn (#lrevalk allknn) tminput,
       combine (map LrMove all_lrchoice,
                infer_knn (#lrpolik allknn) tminput))
    | (true, StopBoard (tm,pos)) =>
      (infer_knn (#stopevalk allknn) tminput,
       combine (map StopMove all_stopchoice,
                infer_knn (#stoppolik allknn) tminput))
    | (true, SubBoard (tm,pos)) =>
      (infer_knn (#subevalk allknn) tminput,
       combine (map SubMove all_subchoice,
                infer_knn (#subpolik allknn) tminput))
     | _ => raise ERR "mk_tnn_fep" ""
  end

(* -------------------------------------------------------------------------
   MCTS big steps: tree neural network
   ------------------------------------------------------------------------- *)

fun n_bigsteps n fep (allex,allroot,endroot) tree =
  if n <= 0 then (allex,allroot,endroot) else
  let
    val sit = #sit (dfind [0] tree)
    val _ = print_endline
      (int_to_string n ^ ": " ^ term_to_string (nntm_of_sit sit))
    val (nsim,decay) = (100,0.99)
    val (tree1,t) = add_time (mcts (nsim,decay) fep status_of apply_move) tree
    val _ = print_endline ("mcts-time :" ^ Real.toString t)
    val cido = select_bigstep tree1 [0]
  in
    case cido of NONE =>
      let val root = dfind [0] tree1 in
        (add_simulex (tree1,allex), root :: allroot, root :: endroot)
      end
   | SOME cid =>
      let
        val root = dfind [0] tree1
        val rootl = root :: allroot
        val tree2 = cut_tree tree1 cid
      in
        print_endline ("  " ^ string_of_move (move_of_cid root cid));
        n_bigsteps (n-1) fep (add_simulex (tree1,allex),rootl,endroot) tree2
      end
  end

fun n_bigsteps_target n fep (target, (allex,allroot,endroot))  =
  let val tree = starttree_of 0.99 fep status_of (p1_startpos target) in
    n_bigsteps n fep (allex,allroot,endroot) tree
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun summary_wins (allroot,endroot) =
  let
    val w1 = length (filter (fn x => status_of (#sit x) = Win) endroot)
    val w2 = length (filter (fn x => #status x = Win) endroot)
    val w3 = length (filter (fn x => #status x = Win) allroot)
  in
    summary ("Wins: " ^ String.concatWith " " (map int_to_string [w1,w2,w3]))
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop: tree neural network
   ------------------------------------------------------------------------- *)

val operl_glob =
  [(F,0),(numtag_var,1)] @ operl_of_term ``SUC 0 + 0 * 0 = 0``;

fun rl_start_one dim targetl =
  let
    val alltnn = random_alltnn dim operl_glob
    val fep = mk_tnn_fep alltnn
    val (new_allex,allroot,endroot) =
      foldl (n_bigsteps_target 50 fep) (empty_allex,[],[]) targetl
  in
    summary_wins (allroot,endroot); discard_oldex new_allex 10000
  end

fun rl_loop_one dim targetl allex =
  let
    val (alltnn,t1) = add_time (train_alltnn dim operl_glob) allex
    val _ = summary ("Training time : " ^ Real.toString t1)
    val fep = mk_tnn_fep alltnn
    val ((new_allex,allroot,endroot),t2) =
      add_time (foldl (n_bigsteps_target 50 fep) (allex,[],[])) targetl
    val _ = summary ("Proving time : " ^ Real.toString t2)
  in
    summary_wins (allroot,endroot); discard_oldex new_allex 10000
  end

fun rl_loop (n,nmax) dim targetl allex =
  if n >= nmax then allex else
    let val newallex = rl_loop_one dim targetl allex in
      summary ("Generation " ^ int_to_string n);
      rl_loop (n + 1, nmax) dim targetl newallex
    end

fun wrap_rl_loop nmax dim targetl =
  let
    val _ = summary "Generation 0"
    val allex = rl_start_one dim targetl
  in
    rl_loop (1,nmax) dim targetl allex
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop: nearest neighbor
   ------------------------------------------------------------------------- *)

fun rlknn_one targetl allex =
  let
    val (allknn,t1) = add_time train_allknn allex
    val _ = summary ("Training time : " ^ Real.toString t1)
    val fep = mk_knn_fep allknn
    val ((new_allex,allroot,endroot),t2) =
      add_time (foldl (n_bigsteps_target 50 fep) (allex,[],[])) targetl
    val _ = summary ("Proving time : " ^ Real.toString t2)
  in
    summary_wins (allroot,endroot); discard_oldex new_allex 10000
  end

fun rlknn_loop (n,nmax) targetl allex =
  if n >= nmax then allex else
    let val newallex = rlknn_one targetl allex in
      summary ("Generation " ^ int_to_string n);
      rlknn_loop (n+1,nmax) targetl newallex
    end

fun wrap_rlknn_loop nmax dim targetl =
  let
    val _ = summary "Generation 0"
    val allex = rl_start_one dim targetl
  in
    rlknn_loop (1,nmax) targetl allex
  end


(*
load "mlTacticData"; load "rlMiniProve";
open aiLib mlTacticData rlMiniProve;

val targetl = data_mg2 ();
val _ = export_terml "/home/thibault/mg2" targetl;
(* val _ = psMCTS.ignorestatus_flag := true; (* doesnt work *) *)
val allex = wrap_rl_loop 10 4 targetl;

val targetl = import_terml "/home/thibault/mg2";
val allex = wrap_rlknn_loop 10 4 targetl;


*)


end (* struct *)
