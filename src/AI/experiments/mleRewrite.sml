(* ========================================================================= *)
(* FILE          : mleRewrite.sml                                            *)
(* DESCRIPTION   : Term rewriting as a reinforcement learning game           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mleRewrite :> mleRewrite =
struct

open HolKernel boolLib Abbrev aiLib smlParallel psMCTS psTermGen
  mlTreeNeuralNetwork mlTacticData mlReinforce mleArithData

val ERR = mk_HOL_ERR "mleRewrite"
fun debug s =
  debug_in_dir (HOLDIR ^ "/src/AI/experiments/debug") "mleRewrite" s

(* -------------------------------------------------------------------------
   Axioms and theorems
   ------------------------------------------------------------------------- *)

val robinson_eq_list =
 [``x + 0 = x``,``x + SUC y = SUC (x + y)``,``x * 0 = 0``,
   ``x * SUC y = x * y + x``]

val robinson_eq_vect = Vector.fromList robinson_eq_list

(* -------------------------------------------------------------------------
   Length of a proof using the left outermost (lo) strategy
   ------------------------------------------------------------------------- *)

fun trySome f l = case l of
    [] => NONE
  | a :: m => (case f a of NONE => trySome f m | SOME b => SOME b)

fun lo_rwpos tm =
  let
    fun f pos =
      let fun test x = isSome (paramod_ground x (tm,pos)) in
        exists test robinson_eq_list
      end
  in
    List.find f (all_pos tm)
  end

fun lo_trace nmax toptm =
  let
    val l = ref []
    val acc = ref 0
    fun loop tm =
      if is_suc_only tm then (SOME (rev (!l),!acc))
      else if !acc > nmax then NONE else
    let
      val pos = valOf (lo_rwpos tm)
      val tm' = valOf (trySome (C paramod_ground (tm,pos)) robinson_eq_list)
    in
      (l := (tm,pos) :: !l; acc := length pos + 1 + !acc; loop tm')
    end
  in
    loop toptm
  end

fun lo_prooflength n tm = snd (valOf (lo_trace n tm))

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type pos = int list
type pb = (term * pos)
datatype board = Board of pb | FailBoard

fun mk_startsit tm = (true, Board (tm,[]))
fun dest_startsit target = case target of
    (true, Board (tm,[])) => tm
  | _ => raise ERR "dest_startsit" ""

fun is_proven (tm,_) = is_suc_only tm

fun status_of sit = case snd sit of
    Board pb => if is_proven pb then Win else Undecided
  | FailBoard => Lose

(* -------------------------------------------------------------------------
   Neural network units and inputs
   ------------------------------------------------------------------------- *)

val numtag = mk_var ("numtag", ``:num -> num``)

fun tag_pos (tm,pos) =
  if null pos then (if is_eq tm then tm else mk_comb (numtag,tm)) else
  let
    val (oper,argl) = strip_comb tm
    fun f i arg = if i = hd pos then tag_pos (arg,tl pos) else arg
  in
    list_mk_comb (oper, mapi f argl)
  end

val rewrite_operl =
  let val operl' = (numtag,1) :: operl_of (``0 * SUC 0 + 0 = 0``) in
    mk_fast_set oper_compare operl'
  end

fun nntm_of_sit sit = case snd sit of
    Board (tm,pos) => tag_pos (tm,pos)
  | FailBoard => T

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Arg of int | Paramod of (int * bool)

val movel =
  map Arg [0,1] @
  [Paramod (0,true),Paramod (0,false)] @
  [Paramod (1,true),Paramod (1,false)] @
  [Paramod (2,true)] @
  [Paramod (3,true),Paramod (3,false)]

fun move_compare (m1,m2) = case (m1,m2) of
    (Arg i1, Arg i2) => Int.compare (i1,i2)
  | (Arg _, _) => LESS
  | (_,Arg _) => GREATER
  | (Paramod (i1,b1), Paramod (i2,b2)) =>
    (cpl_compare Int.compare bool_compare) ((i1,b1),(i2,b2))

fun bts b = if b then "t" else "f"

fun string_of_move move = case move of
    Arg n => ("A" ^ its n)
  | Paramod (i,b) => ("P" ^ its i ^ bts b)

fun narg tm = length (snd (strip_comb tm))

fun argn_pb n (tm,pos) = SOME (tm,pos @ [n])

fun paramod_pb (i,b) (tm,pos) =
  let
    val ax = Vector.sub (robinson_eq_vect,i)
    val tmo = paramod_ground (if b then ax else sym ax) (tm,pos)
  in
    SOME (valOf tmo,[]) handle Option => NONE
  end

fun available (tm,pos) (move,r:real) = case move of
    Arg i => (narg (find_subtm (tm,pos)) >= i + 1)
  | Paramod (i,b) =>
    let val ax = Vector.sub (robinson_eq_vect,i) in
      if b
      then can (paramod_ground ax) (tm,pos)
      else can (paramod_ground (sym ax)) (tm,pos)
    end

fun filter_sit sit = case snd sit of
    Board (tm,pos) => List.filter (available (tm,pos))
  | FailBoard => (fn l => [])

fun apply_move move sit =
  (true, case snd sit of Board pb =>
    Board (valOf (
      case move of
        Arg n => argn_pb n pb
      | Paramod (i,b) => paramod_pb (i,b) pb
    ))
  | FailBoard => raise ERR "move_sub" ""
  )
  handle Option => (true, FailBoard)

(* -------------------------------------------------------------------------
   Target
   ------------------------------------------------------------------------- *)

fun lo_prooflength_target target = case target of
    (true, Board (tm,[])) => lo_prooflength 200 tm
  | _ => raise ERR "lo_prooflength_target" ""

fun write_targetl targetl =
  let val tml = map dest_startsit targetl in
    mlTacticData.export_terml (!parallel_dir ^ "/targetl") tml
  end

fun read_targetl () =
  let val tml = mlTacticData.import_terml (!parallel_dir ^ "/targetl") in
    map mk_startsit tml
  end

fun max_bigsteps target = 2 * lo_prooflength_target target + 1

(* -------------------------------------------------------------------------
   Level
   ------------------------------------------------------------------------- *)

fun create_train_evalsorted () =
  let
    val filein = dataarith_dir ^ "/train"
    val fileout = dataarith_dir ^ "/train_plsorted"
    val l1 = import_terml filein ;
    val l2 = mapfilter (fn x => (x, lo_prooflength 200 x)) l1
    val l3 = filter (fn x => snd x <= 100) l2
    val l4 = dict_sort compare_imin l3
  in
    export_terml fileout (map fst l4)
  end

fun mk_targetl level ntarget =
  let
    val tml = mlTacticData.import_terml (dataarith_dir ^ "/train_plsorted")
    val tmll = map shuffle (first_n level (mk_batch 400 tml))
    val tml2 = List.concat (list_combine tmll)
  in
    map mk_startsit (first_n ntarget tml2)
  end

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val gamespec : (board,move) mlReinforce.gamespec =
  {
  movel = movel,
  move_compare = move_compare,
  string_of_move = string_of_move,
  filter_sit = filter_sit,
  status_of = status_of,
  apply_move = apply_move,
  operl = rewrite_operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  opens = "mleRewrite",
  max_bigsteps = max_bigsteps
  }

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun maxprooflength_atgen () =
  let val tml = import_terml (dataarith_dir ^ "/train_plsorted") in
    map (list_imax o map (lo_prooflength 200)) (mk_batch 400 tml)
  end

fun stats_prooflength file =
  let
    val l0 = import_terml file
    val l1 = mapfilter (fn x => (x,(lo_prooflength 200) x)) l0
    val _  = print_endline (its (length l1))
    val l2 = dlist (dregroup Int.compare (map swap l1))
  in
    map_snd length l2
  end

(* -------------------------------------------------------------------------
   Basic exploration
   ------------------------------------------------------------------------- *)

fun explore_gamespec tm =
  let val dhtnn = random_dhtnn_gamespec gamespec in
    explore_test gamespec dhtnn (mk_startsit tm)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop with fixed parameters
   ------------------------------------------------------------------------- *)

fun reinforce_fixed runname ngen =
  (
  logfile_glob := runname;
  parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^
  (!logfile_glob);
  ncore_mcts_glob := 8;
  ncore_train_glob := 4;
  ntarget_compete := 400;
  ntarget_explore := 400;
  exwindow_glob := 40000;
  uniqex_flag := false;
  dim_glob := 12;
  lr_glob := 0.02;
  batchsize_glob := 16;
  decay_glob := 0.99;
  level_glob := 1;
  nsim_glob := 1600;
  nepoch_glob := 100;
  ngen_glob := ngen;
  start_rl_loop gamespec
  )

(* -------------------------------------------------------------------------
   Final evaluation
   ------------------------------------------------------------------------- *)

fun final_eval dhtnn_name (a,b) testbase =
  let
    val eval_dir = HOLDIR ^ "/src/AI/machine_learning/eval"
    val file = eval_dir ^ "/" ^ dhtnn_name
    val dhtnn = mlTreeNeuralNetwork.read_dhtnn file
    val l1 = import_terml (dataarith_dir ^ "/" ^ testbase)
    val l2 = mapfilter (fn tm => (tm,snd (valOf (lo_trace 200 tm)))) l1
    val l3 = filter (fn x => snd x >= a andalso snd x <= b) l2
  in
    compete_one gamespec dhtnn (map mk_startsit (map fst l3))
  end


end (* struct *)
