(* ========================================================================= *)
(* FILE          : rlEnv.sml                                                 *)
(* DESCRIPTION   : Environnement for reinforcement learning                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlEnv :> rlEnv =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor";
*)

open HolKernel Abbrev boolLib aiLib psMCTS mlTreeNeuralNetwork
rlLib rlTrain

val ERR = mk_HOL_ERR "rlEnv"

val knn_flag = ref false (* use nearest neighbor instead for comparison *)

type ('a,''b,'c,'d) sittools =
  {
  class_of_sit: 'a sit -> ''b,
  mk_startsit: 'c -> 'a sit,
  movel_in_sit: ''b -> 'd list,
  nntm_of_sit: 'a sit -> term,
  sitclassl: ''b list
  }

(* -------------------------------------------------------------------------
   Hard-coded parameters
   ------------------------------------------------------------------------- *)

val exwindow_glob = 10000
val bigsteps_glob = 50
val nsim_glob = 100
val decay_glob = 0.99
val trainsplit_glob = 0.9 (* 10 percent of the data used for testing *)

(* -------------------------------------------------------------------------
   Log
   ------------------------------------------------------------------------- *)

val eval_dir = HOLDIR ^ "/src/AI/reinforcement_learning/eval"
fun log_eval file s =
  let val path = eval_dir ^ "/" ^ file in
    mkDir_err eval_dir;
    append_endline path s
  end

fun summary s = log_eval "rlEnv_test3"  s

(* -------------------------------------------------------------------------
   Evaluation and policy
   ------------------------------------------------------------------------- *)

fun mk_fep_alltnn sittools alltnn sit =
  let
    val sitclass = (#class_of_sit sittools) sit
    val movel = (#movel_in_sit sittools) sitclass
    val (etnn,ptnn) =  assoc sitclass alltnn
    val nntm = (#nntm_of_sit sittools) sit
  in
    (eval_treenn etnn nntm, combine (movel, poli_treenn ptnn nntm))
  end

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

fun update_allex (sitclass,(nntm,(e,p))) allex =
  let
    val (eex,pex) = assoc sitclass allex
    val (neweex,newpex) = ((nntm,e) :: eex, (nntm,p) :: pex)
    fun f x = if fst x = sitclass then (sitclass,(neweex,newpex)) else x
  in
    map f allex
  end

fun update_allex_from_tree sittools tree allex =
  let
    val root = dfind [0] tree
    val epo  = evalpoli_example tree [0]
    val sit  = #sit root
    val nntm = (#nntm_of_sit sittools) sit
  in
    if can (#class_of_sit sittools) sit then
      let val sitclass = (#class_of_sit sittools) sit in
        case epo of
          NONE    => allex
        | SOME ep => update_allex (sitclass,(nntm,ep)) allex
      end
    else allex
  end


fun discard_oldex allex n =
  map_snd (fn (a,b) => (first_n n a, first_n n b)) allex

fun empty_allex sitclassl =
  let fun f _ = ([],[]) in map_assoc f sitclassl end

(* -------------------------------------------------------------------------
   MCTS big steps
   ------------------------------------------------------------------------- *)

fun n_bigsteps (n,nmax) sittools pbspec (allex,allroot,endroot,provenl)
  target tree =
  if n >= nmax then (allex,allroot,endroot,provenl) else
  let
    val nntm_of_sit = #nntm_of_sit sittools
    val sit = #sit (dfind [0] tree)
    val _ = print_endline (int_to_string n ^ ": " ^
                           term_to_string (nntm_of_sit sit))
    val newtree = mcts (nsim_glob, decay_glob) pbspec tree
    val cido = select_bigstep newtree [0]
  in
    case cido of NONE =>
      let
        val root = dfind [0] newtree
        val status = (fst (fst pbspec)) (#sit root)
        val newprovenl = if status = Win then target :: provenl else provenl
      in
        (update_allex_from_tree sittools newtree allex,
         root :: allroot, root :: endroot, newprovenl)
      end
   | SOME cid =>
      let
        val root = dfind [0] newtree
        val newallroot = root :: allroot
        val cuttree = cut_tree newtree cid
        val newallex = update_allex_from_tree sittools newtree allex
      in
        (* print_endline ("  " ^ string_of_move (move_of_cid root cid)); *)
        n_bigsteps (n+1,nmax) sittools pbspec
        (newallex,newallroot,endroot,provenl) target cuttree
      end
  end

fun n_bigsteps_target n sittools pbspec
  (target,(allex,allroot,endroot,provenl)) =
  let
    val mk_startsit = #mk_startsit sittools
    val tree = starttree_of decay_glob pbspec (mk_startsit target)
  in
    n_bigsteps (0,n) sittools pbspec 
    (allex,allroot,endroot,provenl) target tree
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun random_eptnn movel_in_sit (operl,dim) sitclass =
  let val polin = length (movel_in_sit sitclass) in
    (random_treenn (dim,1) operl, random_treenn (dim,polin) operl)
  end

fun train_alltnn movel_in_sit (operl,dim) allex =
  let
    fun f (sitclass,(evalex,poliex)) =
      let val (etnn,ptnn) = random_eptnn movel_in_sit (operl,dim) sitclass in
        (sitclass,
        (train_tnn_eval dim etnn (split_traintest trainsplit_glob evalex),
         train_tnn_poli dim ptnn (split_traintest trainsplit_glob poliex)))
      end
  in
    map f allex
  end

(* -------------------------------------------------------------------------
   Results
   ------------------------------------------------------------------------- *)

fun summary_wins pbspec (allroot,endroot) =
  let
    val status_of = fst (fst pbspec)
    val w1 = length (filter (fn x => status_of (#sit x) = Win) endroot)
    val w2 = length (filter (fn x => #status x = Win) endroot)
    val w3 = length (filter (fn x => #status x = Win) allroot)
  in
    summary ("Wins: " ^ String.concatWith " " (map int_to_string [w1,w2,w3]))
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun explore_f sittools pbspec allex targetl =
  let
    val ((new_allex,allroot,endroot,provenl),t) =
      add_time (foldl (n_bigsteps_target bigsteps_glob sittools pbspec)
      (allex,[],[],[])) targetl
    val _ = summary ("Exploration time : " ^ Real.toString t)
    val _ = summary_wins pbspec (allroot,endroot)
  in
    (new_allex,provenl)
  end

fun train_f movel_in_sit tnnspec allex =
  let
    val (alltnn,t) = add_time (train_alltnn movel_in_sit tnnspec) allex
    val _ = summary ("Training time : " ^ Real.toString t)
  in
    alltnn
  end

fun rl_start sittools tnnspec rulespec targetdata =
  let
    val _ = summary "Generation 0"
    val sitclassl = #sitclassl sittools
    val alltnn =
      map_assoc (random_eptnn (#movel_in_sit sittools) tnnspec) sitclassl
    val pbspec = (rulespec, mk_fep_alltnn sittools alltnn)
    val allex = empty_allex sitclassl
    val targetl = first_n 200 (snd targetdata)
    val (new_allex,provenl) = explore_f sittools pbspec allex targetl
  in
    (discard_oldex new_allex exwindow_glob,provenl)
  end

fun rl_one n sittools tnnspec rulespec targetl allex =
  let
    val _ = summary ("Generation " ^ int_to_string n)
    val alltnn = train_f (#movel_in_sit sittools) tnnspec allex
    val pbspec = (rulespec, mk_fep_alltnn sittools alltnn)
    val (newallex,provenl) = explore_f sittools pbspec allex targetl
  in
    (discard_oldex newallex exwindow_glob,provenl)
  end

fun rl_loop (n,nmax) sittools tnnspec rulespec 
  targetdata update_targetdata allex =
  if n >= nmax then (targetdata,allex) else
    let
      val targetl = first_n 200 (snd targetdata) (* match rlData value *)
      val (newallex,provenl) =
      rl_one n sittools tnnspec rulespec targetl allex
      (* todo: make generic *)
      val newtargetdata = update_targetdata provenl targetdata
    in
      rl_loop (n+1, nmax) sittools tnnspec rulespec 
      newtargetdata update_targetdata newallex
    end

fun start_rl_loop nmax sittools tnnspec rulespec targetdata update_targetdata =
  let 
    val (allex,provenl) = rl_start sittools tnnspec rulespec targetdata 
    val newtargetdata = update_targetdata provenl targetdata
  in
    rl_loop (1,nmax) sittools tnnspec rulespec newtargetdata update_targetdata allex
  end

(*
load "rlLib"; load "rlGameCopy"; load "rlEnv"; load "rlData";
load "psMCTS";
open aiLib psMCTS rlLib rlGameCopy rlEnv rlData;
ignorestatus_flag := true;
val operl = (numtag_var,1) :: operl_of_term ``SUC 0 + 0 = 0``;
val dim = 6;
val tnnspec = (operl,dim);
val targetdata = init_incdata ();
val nmax = 10;
val allex = start_rl_loop nmax sittools tnnspec rulespec targetdata update_incdata;
*)



end (* struct *)
