(* ========================================================================= *)
(* FILE          : mleSetSynt.sml                                            *)
(* DESCRIPTION   : Specification of a term synthesis game                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSetSynt :> mleSetSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlTreeNeuralNetwork mlTacticData mlReinforce mleLib mleSetLib

val ERR = mk_HOL_ERR "mleSetSynt"

(* -------------------------------------------------------------------------
   Graph
   ------------------------------------------------------------------------- *)

val graphcat = mk_var ("graphcat", ``:bool -> bool -> bool``)

fun mk_graph n t = 
  map (eval_subst (xvar,t) o nat_to_bin) (List.tabulate (n,I))

fun graph_to_term graph =
  let val l = map (fn x => if x then T else F) graph in
    list_mk_binop graphcat l
  end

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = ((term * (bool list * term)) * term)

fun mk_startsit tm = 
  let 
    val graph = mk_graph 16 tm
    val graphtm = graph_to_term graph
  in
    ((tm,(graph,graphtm)),start_form)
  end
  handle HOL_ERR _ => raise ERR "mk_startsit" (term_to_string tm)

fun dest_startsit ((tm,_),_) = tm

val adjgraph = mk_var ("adjgraph", ``: bool -> bool -> bool``);

val operl = 
  mk_fast_set oper_compare
  ( 
    operl_of (listSyntax.mk_list (yvarl,alpha)) @
    map_assoc arity_of (F :: T :: graphcat :: adjgraph :: operl_ext) 
  );

fun nntm_of_sit ((_,(_,graphtm)),tm) = list_mk_comb (adjgraph,[graphtm,tm]);

fun is_end tm = not (can (find_term is_cont) tm);

fun alt_size t = 
  let val (oper,argl) = strip_comb t in
    if is_cont oper then 1 else 1 + sum_int (map alt_size argl)
  end

fun status_of ((orgtm,(graph,graphtm)),tm) =
  if is_end tm then 
    if graph = mk_graph 16 tm handle HOL_ERR _ => false then Win else Lose
  else if alt_size tm > 2 * term_size orgtm + 1 
    then Lose
    else Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term
fun apply_move_to_board move (ctxt,tm) = (ctxt, apply_move move tm)
fun filter_sit (ctxt,tm) = (fn l => filter (is_applicable tm o fst) l)
fun string_of_move tm = tts tm

fun write_targetl file targetl =
  let val tml = map dest_startsit targetl in
    export_terml (file ^ "_targetl") tml
  end

fun read_targetl file =
  let val tml = import_terml (file ^ "_targetl") in
    map mk_startsit tml
  end

fun max_bigsteps ((orgtm,_),_) = 2 * alt_size orgtm + 5

(* -------------------------------------------------------------------------
   Level
   ------------------------------------------------------------------------- *)

val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"

val train_file = datasetsynt_dir ^ "/train_lisp"

fun eval64 t = 
  let 
    val l = List.tabulate (64,I)
    fun f x = (eval_subst (xvar,t) (nat_to_bin x), x)
  in
    SOME (map f l)
  end
  handle HOL_ERR _ => NONE

fun export_setsyntdata () =
  let
    val formgraphl = parse_setsyntdata ()
    val l2 = map_assoc (eval64 o fst) formgraphl;
    val l3 = filter (isSome o snd) l2
    fun cmp (a,b) = Int.compare (term_size a, term_size b) 
  in
    export_terml (datasetsynt_dir ^ "/h4setsynt") 
    (dict_sort cmp (map (fst o fst) l3))
  end

fun mk_targetl level ntarget = 
  let 
    val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt")
    val tmll2 = map shuffle (first_n level (mk_batch_full 400 tml1))
    val tml3 = List.concat (list_combine tmll2)
  in 
    map mk_startsit (first_n ntarget tml3)
  end

(*
load "mleSetSynt"; open mleSetSynt; 
(* export_setsyntdata (); *)

 let
    val tml1 = import_terml (dataarith_dir ^ "/" ^ basein)
    val tmll2 = map shuffle (first_n level (mk_batch 400 tml1))
    val tml3 = List.concat (list_combine tmll2)
  in
    map mk_startsit (first_n ntarget tml3)
  end
*)

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val gamespec =
  {
  movel = movel,
  move_compare = Term.compare,
  status_of = status_of,
  filter_sit = filter_sit,
  apply_move = apply_move_to_board,
  operl = operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  string_of_move = string_of_move,
  max_bigsteps = max_bigsteps
  }

val extspec = mk_extspec "mleSetSynt.extspec" gamespec
(* val test_setsynt_extspec =
  test_mk_extspec "mleSetSynt.test_setsynt_extspec" setsynt_gamespec *)

(* -------------------------------------------------------------------------
   Reinforcement learning
   ------------------------------------------------------------------------- *)

(*
load "mleSetSynt"; open mleSetSynt;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mlReinforce"; open mlReinforce;
load "smlParallel"; open smlParallel;
load "aiLib"; open aiLib;

ncore_mcts_glob := 32;
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
ngen_glob := 100;

logfile_glob := "aa_mleSetSynt1";
parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^ (!logfile_glob);
val r = start_rl_loop (gamespec,extspec);
*)

(* -------------------------------------------------------------------------
   Small test
   ------------------------------------------------------------------------- *)

(*
load "mleSetLib"; open mleSetLib;
load "mleSetSynt"; open mleSetSynt;
load "mlReinforce"; open mlReinforce;
load "psMCTS"; open psMCTS;
nsim_glob := 10000;
decay_glob := 0.99;
val formula = (funpow 20 random_step) start_form;

val formula = ``(qEXISTS_IN (vY0 :'a) (vX:'a) 
(oNOT (pEQ (vX:'a) (vY0 :'a):bool):bool):bool)``;
val formula = ``(oNOT (pEQ (vX :'a) (vX:'a):bool):bool)``;

val formula = ``(qEXISTS_IN (vY0 :'a) (vX:'a) 
(oNOT (pSubq (vX:'a) ((tPower (vY0:'a)) :'a):bool):bool):bool)``;

val board = mk_startsit formula;
val _ = n_bigsteps_test gamespec (random_dhtnn_gamespec gamespec) board;

val tree = mcts_test 10000 gamespec (random_dhtnn_gamespec gamespec) board;
val nodel = trace_win (#status_of gamespec) tree [];
*)
(* 
   todo: have operators with fixed embeddings. i.e no updates
   during learning and fixed 
*)

(* -------------------------------------------------------------------------
   Final test
   ------------------------------------------------------------------------- *)

(*
fun final_stats l =
  let
    val winl = filter (fn (_,b,_) => b) l
    val a = length winl
    val atot = length l
    val b = sum_int (map (fn (_,_,n) => n) winl)
    val btot = sum_int (map (fn (t,_,_) =>
      (term_size o dest_startsit) t) winl)
  in
    ((a,atot,int_div a atot), (b,btot, int_div b btot))
  end

fun final_eval fileout dhtnn set =
  let
    val l = test_compete test_eval_extspec dhtnn (map mk_startsit set)
    val ((a,atot,ar),(b,btot,br)) = final_stats l
    val cr = br * ar + 2.0 * (1.0 - ar)
    val s =
      String.concatWith " " [its a,its atot,rts ar,
                             its b,its btot,rts br,rts cr]
  in
    writel fileout [fileout,s]
  end
*)

(*
load "aiLib"; open aiLib;
load "mleArithData"; open mleArithData;
load "mleLib"; open mleLib;
load "mlReinforce"; open mlReinforce;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "psMCTS"; open psMCTS;
load "mlTacticData"; open mlTacticData;
load "mleSetSynt"; open mleSetSynt;

decay_glob := 0.99;
ncore_mcts_glob := 40;

val testset = import_terml (dataarith_dir ^ "/test");
fun read_ndhtnn n =
  read_dhtnn (eval_dir ^ "/mleSetSynt_eval1_gen" ^ its n ^ "_dhtnn");

val genl = [0,10,99];
val nsiml = [1,16,160,1600];
val paraml = cartesian_product nsiml genl;

fun final_eval_one (nsim,ndhtnn) =
  let
    val dhtnn = read_ndhtnn ndhtnn
    val _ = nsim_glob := nsim
    val suffix =  "ngen" ^ its ndhtnn ^ "-nsim" ^ its nsim
    val file = eval_dir ^ "/a_synteval_" ^ suffix
  in
    final_eval file dhtnn testset
  end;

val _ = app final_eval_one paraml;
*)

(*
load "mleLib"; open mleLib;
load "mleSetLib"; open mleSetLib;
load "aiLib"; open aiLib;

val graph = start_graph formula;
*)




end (* struct *)
