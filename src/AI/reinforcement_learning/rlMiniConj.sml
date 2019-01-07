(* ========================================================================= *)
(* FILE          : rlMiniConj.sml                                          *)
(* DESCRIPTION   : Extract examples form proofs                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlMiniConj :> rlMiniConj =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor";
*)

open HolKernel Abbrev boolLib aiLib rlLib psMCTS mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlMiniConj"

(* -------------------------------------------------------------------------
   Evaluation log
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/reinforcement_learning/eval"
fun log_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end
fun summary s = log_eval "rlMiniConj_knn" s

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

datatype board = ImitBoard of (term * term) | EndBoard of (term * term)

type situation = bool * board

fun status_of sit = case sit of
     (true, EndBoard (tm1,tm2)) => (if tm1 = tm2 then Win else Lose)
   | (true, ImitBoard (tm1,tm2)) =>
     (if term_size tm2 > term_size tm1 then Lose else Undecided)
   | _ => Undecided

fun p1_startpos target = (true, ImitBoard (target,active_var))

(* -------------------------------------------------------------------------
   Rules
   ------------------------------------------------------------------------- *)

datatype imitchoice = ImitZero | ImitSuc | ImitAdd
val all_imitchoice = [ImitZero,ImitSuc,ImitAdd]
fun string_of_imitchoice imit = case imit of
    ImitZero => "ImitZero"
  | ImitAdd  => "ImitAdd"
  | ImitSuc  => "ImitSuc"

val subzero = [{redex = active_var, residue = zero},
               {redex = pending_var, residue = active_var}];
val subsuc = [{redex = active_var, residue = mk_suc active_var}];
val subadd = [{redex = active_var, residue = mk_add (active_var,pending_var)}];

fun apply_imit imit tm = case imit of
    ImitZero => subst_occs [[1],[1]] subzero tm
  | ImitSuc  => subst_occs [[1]] subsuc tm
  | ImitAdd  => subst_occs [[1]] subadd tm

fun move_imit imit sit = case sit of (p, ImitBoard (tm1,tm2)) =>
    let val newtm2 = apply_imit imit tm2 in
      if is_subtm active_var newtm2
      then (p, ImitBoard (tm1,newtm2))
      else (p, EndBoard (tm1,newtm2))
    end
  | _ => raise ERR "move_imit" ""

val apply_move = move_imit

(* -------------------------------------------------------------------------
   Evaluation/Policy
   ------------------------------------------------------------------------- *)

fun nntm_of_sit sit = case sit of
    (true, ImitBoard (tm1,tm2)) => mk_eq (tm1,tm2)
  | (true, EndBoard (tm1,tm2)) => mk_eq (tm1,tm2)
  | _ => raise ERR "nntm_of_sit" ""

fun mk_fep_tnn (evaltnn,politnn) sit = case sit of
    (true, ImitBoard (tm,res)) =>
    let val tminput = nntm_of_sit sit in
      (eval_treenn evaltnn tminput,
       combine (all_imitchoice, poli_treenn politnn tminput))
    end
  | _ => raise ERR "mk_fep_tnn" ""

fun mk_fep_knn (evalknn,poliknn) sit = case sit of
    (true, ImitBoard (tm,res)) =>
    let val tminput = nntm_of_sit sit in
      (infer_knn evalknn tminput,
       combine (all_imitchoice, infer_knn poliknn tminput))
    end
  | _ => raise ERR "mk_fep_knn" ""

(* -------------------------------------------------------------------------
   MCTS big steps
   ------------------------------------------------------------------------- *)

fun add_simulex (tree,(evalex,poliex)) =
  let
    val root = dfind [0] tree
    val polio = poli_example tree [0]
    val evalsc = eval_example tree [0]
    val nntm = nntm_of_sit (#sit root)
  in
    (
    (nntm,evalsc) :: evalex,
    case polio of
      NONE => poliex
    | SOME polisc => (nntm,polisc) :: poliex
    )
  end

fun discard_oldex (evalex,poliex) n = (first_n n evalex, first_n n poliex)

val empty_allex = ([],[])

fun n_bigsteps n fep (allex,allroot,endroot) tree =
  if n <= 0 then (allex,allroot,endroot) else
  let
    val sit = #sit (dfind [0] tree)
    val _ = print_endline (int_to_string n ^ ": " ^
                           term_to_string (nntm_of_sit sit))
    val (nsim,decay) = (100,0.99)
    val (tree1,t) = add_time (mcts (nsim,decay) fep status_of apply_move) tree
    val _ = print_endline ("mcts time :" ^ Real.toString t)
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
        print_endline ("  " ^ string_of_imitchoice (move_of_cid root cid));
        n_bigsteps (n-1) fep (add_simulex (tree1,allex),rootl,endroot) tree2
      end
  end

fun n_bigsteps_target n fep (target, (allex,allroot,endroot))  =
  let val tree = starttree_of 0.99 fep status_of (p1_startpos target) in
    n_bigsteps n fep (allex,allroot,endroot) tree
  end

(* -------------------------------------------------------------------------
   Training (copied from rlMiniTrain)
   ------------------------------------------------------------------------- *)

fun random_alltnn dim operl =
  (random_treenn (dim,1) operl,
   random_treenn (dim,length all_imitchoice) operl)

fun train_tnn dim operl (evalex,poliex) =
  let val randalltnn = random_alltnn dim operl in
    (
    train_tnn_eval dim (fst randalltnn) (split_traintest 0.9 evalex),
    train_tnn_poli dim (snd randalltnn) (split_traintest 0.9 poliex)
    )
  end

val operl_glob =
  [(active_var,0),(pending_var,0)] @ operl_of_term ``(SUC 0 + 0 * 0 = 0)``;

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

fun rl_start dim targetl =
  let
    val alltnn = random_alltnn dim operl_glob
    val fep = mk_fep_tnn alltnn
    val (new_allex,allroot,endroot) =
      foldl (n_bigsteps_target 50 fep) (empty_allex,[],[]) targetl
  in
    summary_wins (allroot,endroot); discard_oldex new_allex 10000
  end

fun rl_one dim targetl allex =
  let
    val (alltnn,t1) = add_time (train_tnn dim operl_glob) allex
    val fep = mk_fep_tnn alltnn
    val _ = summary ("Training time : " ^ Real.toString t1)
    val ((new_allex,allroot,endroot),t2) =
      add_time (foldl (n_bigsteps_target 50 fep) (allex,[],[])) targetl
    val _ = summary ("Proving time : " ^ Real.toString t2)
  in
    summary_wins (allroot,endroot); discard_oldex new_allex 10000
  end

fun rl_loop (n,nmax) dim targetl allex =
  if n >= nmax then allex else
    let val newallex = rl_one dim targetl allex in
      summary ("Generation " ^ int_to_string n);
      rl_loop (n + 1, nmax) dim targetl newallex
    end

fun wrap_rl_loop nmax dim targetl =
  let
    val _ = summary "Generation 0"
    val allex = rl_start dim targetl
  in
    rl_loop (1,nmax) dim targetl allex
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop: nearest neighbor
   ------------------------------------------------------------------------- *)

fun rlknn_one targetl allex =
  let
    val allknn = (train_knn (fst allex), train_knn (snd allex))
    val fep = mk_fep_knn allknn
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
      rlknn_loop (n+1, nmax) targetl newallex
    end

fun wrap_rlknn_loop nmax dim targetl =
  let
    val _ = summary "Generation 0"
    val allex = rl_start dim targetl
  in
    rlknn_loop (1,nmax) targetl allex
  end

(*
load "mlTacticData"; load "rlMiniEx"; load "rlMiniConj";
open aiLib mlTacticData rlMiniEx rlMiniConj;
val targetl = data_mg3 ();
export_terml "/home/thibault/mg3" targetl;
val (evalex,poliex) = wrap_rl_loop 10 4 targetl;

load "mlTacticData"; load "rlMiniConj";
open aiLib mlTacticData rlMiniConj;
val targetl = import_terml "/home/thibault/mg3";
val allex = wrap_rlknn_loop 10 4 targetl;

*)



end (* struct *)
