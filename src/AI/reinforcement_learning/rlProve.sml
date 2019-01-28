(* ========================================================================= *)
(* FILE          : rlProve.sml                                               *)
(* DESCRIPTION   : Datatypes for the robber theorem prover                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlProve :> rlProve =
struct

open HolKernel Abbrev boolLib aiLib
  mlTreeNeuralNetwork psMCTS rlLib rlRules rlTrain

val ERR = mk_HOL_ERR "rlProve"

(* -------------------------------------------------------------------------
   Evaluation log
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/reinforcement_learning/eval"
fun log_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end
fun summary s = log_eval "summary" s

(* -------------------------------------------------------------------------
   Status
   ------------------------------------------------------------------------- *)

fun p1_startpos target = (true, TacBoard target)

type situation = bool * board

fun decide tm =
  let
    val thm1 = SYM (SPEC_ALL arithmeticTheory.ADD_SUC)
    val thm2 = arithmeticTheory.ADD_0
    val (gl,_) = REWRITE_TAC [thm1,thm2] ([],tm)
  in
    null gl
  end
  handle Interrupt => raise Interrupt | _ => false

fun status_of sit = case sit of
    (true, TacBoard tm) =>
      if tm = F orelse not (decide tm) then Lose
      else if not (null (match_axiom tm)) then Win
      else Undecided
  | (true, ImitBoard ((tm,pos),res)) =>
     let val red = subtm_at_pos pos tm in
       if term_size res > term_size red
       then Lose
       else Undecided
     end
  | _ => Undecided

(* -------------------------------------------------------------------------
   Evaluation/Policy
   ------------------------------------------------------------------------- *)

fun fevalpoli alltnn sit = case sit of
    (true, TacBoard tm) =>
    let val tminput = nntm_of_sit sit in
      (eval_treenn (#taceval alltnn) tminput,
       combine (map TacMove all_tacchoice,
                poli_treenn (#tacpoli alltnn) tminput))
    end
  | (true, StopBoard (tm,pos)) =>
    let val tminput = nntm_of_sit sit in
      (eval_treenn (#stopeval alltnn) tminput,
       combine (map StopMove all_stopchoice,
                poli_treenn (#stoppoli alltnn) tminput))
    end
  | (true, LrBoard (tm,pos)) =>
    let val tminput = nntm_of_sit sit in
      (eval_treenn (#lreval alltnn) tminput,
       combine (map LrMove all_lrchoice,
                poli_treenn (#lrpoli alltnn) tminput))
    end
  | (true, ImitBoard ((tm,pos),res)) =>
    let val tminput = nntm_of_sit sit in
      (eval_treenn (#imiteval alltnn) tminput,
       combine (map ImitMove all_imitchoice,
                poli_treenn (#imitpoli alltnn) tminput))
    end
  | (false, ConjunctBoard (tm1,tm2)) =>
    let val tminput = nntm_of_sit sit in
      (eval_treenn (#conjuncteval alltnn) tminput,
       combine (map ConjunctMove all_conjunctchoice,
                poli_treenn (#conjunctpoli alltnn) tminput))
    end
  | _ => raise ERR "fevalpoli" ""


(* -------------------------------------------------------------------------
   MCTS big steps
   ------------------------------------------------------------------------- *)

fun n_bigsteps n fep (allex,allroot) tree =
  if n <= 0 then (allex,allroot) else
  let
    val sit = #sit (dfind [0] tree)
    val _ = print_endline (int_to_string n ^ ": " ^
                           term_to_string (nntm_of_sit sit))
    val (nsim,decay) = (1600,0.99)
    val (tree1,t) = add_time (mcts (nsim,decay) fep status_of apply_move) tree
    val _ = print_endline ("mcts time :" ^ Real.toString t)
    val cido = select_bigstep tree1 [0]
  in
    case cido of NONE =>
      let val root = dfind [0] tree1 in
        if #vis root > 1.5
        then (add_simulex (tree1,allex), root :: allroot)
        else (allex, root :: allroot)
      end
   | SOME cid =>
      let
        val root = dfind [0] tree1
        val rootl = root :: allroot
        val tree2 = cut_tree tree1 cid
      in
        print_endline ("  " ^ string_of_move (move_of_cid root cid));
        if #vis root > 1.5
        then n_bigsteps (n-1) fep (add_simulex (tree1,allex),rootl) tree2
        else n_bigsteps (n-1) fep (allex,rootl) tree2
      end
  end

fun n_bigsteps_target n alltnn (target, (allex,allroot))  =
  let
    val fep    = fevalpoli alltnn
    val decay  = 0.99
    val tree   = starttree_of decay fep status_of (p1_startpos target)
  in
    n_bigsteps n fep (allex,allroot) tree
  end

(* -------------------------------------------------------------------------
   Curriculum : list of targets
   ------------------------------------------------------------------------- *)

fun mk_nsuc n = if n = 0 then ``0`` else mk_suc (mk_nsuc (n-1));

fun add_to_n n =
  if n < 2 then [] else
  let
    val l = number_partition 2 n
    fun f x =
      let val (a,b) = pair_of_list x in
        mk_eq (mk_add (mk_nsuc a, mk_nsuc b), mk_nsuc n)
      end
  in
    map f l
  end

fun my_dupl n l = if n <= 1 then l else l @ my_dupl (n-1) l

fun mk_level n =
  let val tml1 = List.concat (List.tabulate (n+1,add_to_n)) in
    first_n 100 (my_dupl ((100 div (length tml1)) + 1) tml1)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

val operl = extra_operl @ operl_of_term ``(SUC 0 + 0 = 0) /\ (0 = 0)``;
val dim_glob = 10

fun rl_start_one level =
  let
    val targetl = mk_level level
    val alltnn = random_alltnn dim_glob operl
    val (new_allex,allroot) =
      foldl (n_bigsteps_target 50 alltnn) (empty_allex,[]) targetl
    val nw2 = length (filter (fn x => #status x = Win) allroot)
    val nw1 = length (filter (fn x => status_of (#sit x) = Win) allroot)
  in
    summary ("Wins: " ^ int_to_string nw1 ^ " " ^ int_to_string nw2);
    (discard_oldex new_allex 10000,
     if nw1 > (length targetl) div 2
     then (summary "Level up"; level + 1)
     else level)
  end

fun rl_loop_one (allex,level) =
  let
    val (alltnn,t1) = add_time (all_train dim_glob operl) allex
    val _ = summary ("Training time : " ^ Real.toString t1)
    val targetl = mk_level level
    val ((new_allex,allroot),t2) =
      add_time (foldl (n_bigsteps_target 50 alltnn) (allex,[])) targetl
    val _ = summary ("Proving time : " ^ Real.toString t2)
    val nw2 = length (filter (fn x => #status x = Win) allroot)
    val nw1 = length (filter (fn x => status_of (#sit x) = Win) allroot)
  in
    summary ("Wins: " ^ int_to_string nw1 ^ " " ^ int_to_string nw2);
    (discard_oldex new_allex 10000,
     if nw1 > (length targetl) div 2
     then (summary "Level up"; if level < 10 then level + 1 else level)
     else level)
  end

fun rl_loop (ncount,nmax) r =
  if ncount >= nmax then r else
    let val newr = rl_loop_one r in
      summary ("Generation " ^ int_to_string ncount);
      rl_loop (ncount + 1, nmax) newr
    end

fun wrap_rl_loop nmax =
  let val r = rl_start_one 3 in rl_loop (1,nmax) r end

(*
load "rlProve"; load "rlTrain";
open aiLib psMCTS rlLib rlRules rlProve mlTreeNeuralNetwork rlTrain;
val (allex,level) = wrap_rl_loop 100;
*)

(* todo run eprover experiments on dependencies of list *)

end (* struct *)
