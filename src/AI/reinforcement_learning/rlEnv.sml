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

val exwindow_glob = 100000
val bigsteps_glob = 50
val nsim_glob = 400
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

fun summary s = log_eval "rlEnv_test8"  s

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
    val epo  = evalpoli_example tree
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

fun n_bigsteps_loop (n,nmax) sittools pbspec (allex,allroot) tree =
  if n >= nmax then (allex,allroot) else
  let
    val nntm_of_sit = #nntm_of_sit sittools
    val sit = #sit (dfind [0] tree)
    val _ = print_endline (int_to_string n ^ ": " ^
                           term_to_string (nntm_of_sit sit))
    val newtree = mcts (nsim_glob, decay_glob) pbspec tree
    val root = dfind [0] newtree
    val cido = select_bigstep newtree [0]
  in
    case cido of
     NONE => (allex, root :: allroot)
   | SOME cid =>
      let
        val cuttree = cut_tree newtree cid
        val newallex = update_allex_from_tree sittools newtree allex
      in
        (* print_endline ("  " ^ string_of_move (move_of_cid root cid)); *)
        n_bigsteps_loop (n+1,nmax) sittools pbspec
        (newallex, root :: allroot) cuttree
      end
  end

fun n_bigsteps n sittools pbspec target =
  let
    val mk_startsit = #mk_startsit sittools
    val tree = starttree_of decay_glob pbspec (mk_startsit target)
    val allex = empty_allex (#sitclassl sittools)
  in
    n_bigsteps_loop (0,n) sittools pbspec (allex,[]) tree
  end

(*
  val status = (fst (fst pbspec)) (#sit root)
  val newprovenl = if status = Win then target :: provenl else provenl
*)
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

fun summary_wins pbspec allrootl =
  let
    val endrootl = map hd allrootl
    val startrootl = map last allrootl
    fun value x = #sum x / #vis x
    val w5 = average_real (map value startrootl)
    val status_of = fst (fst pbspec)
    val w1 = length (filter (fn x => status_of (#sit x) = Win) endrootl)
    val w2 = length (filter (fn x => #status x = Win) endrootl)
    val w3 = length (filter (fn x => #status x = Win) (List.concat allrootl))
    val w4 = length (filter (fn x => #status x = Win) startrootl)
    val r1 = Real.fromInt (length (List.concat allrootl)) / 50.0
    val r2 = Real.fromInt w3 / 50.0
  in
    summary ("Win start: " ^ int_to_string w4);
    summary ("Value start: " ^ Real.toString w5);
    summary ("Win end: " ^ String.concatWith " " (map int_to_string [w1,w2]));
    summary ("Big steps (average): " ^ Real.toString r1);
    summary ("Win nodes (average): " ^ Real.toString r2)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun merge_ex (exl,allex) =
  let
    val l = combine (exl,allex)
    fun f ((_,(e1,p1)),(x,(e2,p2))) = (x, (e1 @ e2, p1 @ p2))
  in
    map f l
  end

fun explore_f sittools pbspec allex targetl =
  let
    val (result,t) =
      add_time (map (n_bigsteps bigsteps_glob sittools pbspec)) targetl
    val (allexl,allrootl) = split result
    val _ = summary ("Exploration time : " ^ Real.toString t)
    val _ = summary_wins pbspec allrootl
    val newallex = foldl merge_ex allex allexl
  in
    (newallex,[])
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
    val targetl = first_n 50 (snd targetdata)
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
  if n >= nmax then (allex,targetdata) else
    let
      val targetl = first_n 50 (snd targetdata) (* match rlData value *)
      val (newallex,provenl) = rl_one n sittools tnnspec rulespec targetl allex
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

val targetdata = init_incdata ();

fun update_incdata _ x = x;
val nmax = 20;
val (allex,targetdata) = start_rl_loop nmax sittools tnnspec rulespec targetdata update_incdata;


(* post analysis *)
val (evalex, poliex) = snd (hd allex);
length (fst targetdata);
open mlTreeNeuralNetwork rlTrain;
val etnn = random_treenn (dim,1) operl;
val etnn' = train_tnn_eval dim etnn (split_traintest 0.9 evalex);
*)



end (* struct *)
