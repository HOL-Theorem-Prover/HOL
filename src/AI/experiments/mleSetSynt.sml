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
   Helpers
   ------------------------------------------------------------------------- *)

val uncont_term = mk_var ("uncont_term",alpha)
val uncont_form = mk_var ("uncont_form",bool)
val uncontl = [uncont_term,uncont_form]

fun rw_to_uncont t =
  let val (oper,argl) = strip_comb t in
    if term_eq oper cont_term then uncont_term
    else if term_eq oper cont_form then uncont_form
    else list_mk_comb (oper, map rw_to_uncont argl)
  end

(* -------------------------------------------------------------------------
   Graph
   ------------------------------------------------------------------------- *)






(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = ((term * bool list) * term)

fun string_of_board ((_,bl),tm) =
  String.concatWith " " (map bts bl) ^ " :\n" ^ tts tm

fun mk_graph n t = 
  map (eval_subst (xvar,t) o nat_to_bin) (List.tabulate (n,I))

fun mk_startboard tm = 
  let 
    val graph = mk_graph 12 tm
    val graphtm = term_of_graph graph
  in
    ((tm,(graph,graphtm)),start_form)
  end

fun dest_startboard ((tm,_),_) = tm

fun status_of ((orgtm,graph),tm) =
  if not (can (find_term is_cont) tm) then 
    if graph = mk_graph 12 tm handle HOL_ERR _ => false 
    then Win 
    else Lose
  else if term_size (rw_to_uncont tm) > 2 * term_size orgtm
    then Lose
    else Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term

fun apply_move move (ctxt,tm) = (ctxt, apply_move_aux move tm)
fun available_move board move = available_move_aux (snd board) move
fun string_of_move move = tts move

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (boad,move) game =
  {
  string_of_board = string_of_board,
  movel = movel,
  move_compare = Term.compare,
  string_of_move = string_of_move,
  status_of = status_of,
  available_move = available_move,
  apply_move = apply_move
  }

(* -------------------------------------------------------------------------
   Big steps limit (redundant with status_of)
   ------------------------------------------------------------------------- *)

fun max_bigsteps ((orgtm,_),_) = 2 * term_size orgtm

(* -------------------------------------------------------------------------
   Double-headed neural network
   ------------------------------------------------------------------------- *)

(*
val graphcat = mk_var ("graphcat", ``:bool -> bool -> bool``)
fun term_of_graph graph =
  let val l = map (fn x => if x then T else F) graph in
    list_mk_binop graphcat l
  end
*)

val graphtag = mk_var ("graphtag", ``:bool -> bool``)

fun term_of_graph graph =
  let 
    val vs = "n" ^ String.concat (map (fn x => if x then "1" else "0") graph)
  in
    mk_comb (graphtag, mk_var (vs,bool))
  end

fun mk_graph n t = 
  map (eval_subst (xvar,t) o nat_to_bin) (List.tabulate (n,I))

val adjgraph = mk_var ("adjgraph", ``: bool -> bool -> bool``);

val operl = 
  mk_fast_set oper_compare
  (map_assoc arity_of (graphtag :: adjgraph :: (uncontl @ operl_plain)));

fun term_of_board ((_,graph),tm) = 
  let val graphtm = term_of_graph graph in
    list_mk_comb (adjgraph, [graphtm, rw_to_uncont tm]);

val dhtnn_param =
  {
  operl = operl,
  nlayer_oper = 1, 
  nlayer_headeval = 1, 
  nlayer_headpoli = 1,
  dimin = 8, 
  dimpoli = length movel
  }

(* -------------------------------------------------------------------------
   Levels
   ------------------------------------------------------------------------- *)

val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"

val train_file = datasetsynt_dir ^ "/train_lisp"

fun eval64 t = 
  let 
    val l = List.tabulate (64,I)
    fun f x = (eval_subst (xvar,t) (nat_to_bin x), x)
  in
    map snd (filter fst (map f l))
  end
  handle HOL_ERR _ => raise ERR "eval64" (term_to_string t)

fun bin_to_string bin = String.concatWith "," (map its bin)

fun export_setsyntdata () =
  let
    val formgraphl = parse_setsyntdata ()
    val _ = print_endline ("Reading " ^ its (length formgraphl) ^ " terms");
    val l1 = map (fn (a,b) => (norm_bvarl a ,rev b)) formgraphl
    val l2 = map_assoc (eval64 o fst) l1
    fun f ((a,b),c) = 
      if b = c then () else 
        (
        print_endline (bin_to_string b);
        print_endline (bin_to_string c);
        raise ERR "not_equal_on" (term_to_string a)
        )
    val _ = app f l2
    val tml = map (fst o fst) l2
    fun g tm = 
      if can imitate tm then () else 
        raise ERR "cannot replicate" (term_to_string tm)
    val _ = app g tml
  in
    print_endline ("Exporting " ^ its (length tml) ^ " terms");
    export_terml (datasetsynt_dir ^ "/h4setsynt") 
      (dict_sort tmsize_compare tml)
  end

fun level_targetl level ntarget = 
  let 
    val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt")
    val tmll2 = map shuffle (first_n level (mk_batch_full 400 tml1))
    val tml3 = List.concat (list_combine tmll2)
  in 
    map mk_startboard (first_n ntarget tml3)
  end

val level_param =
  {
  ntarget_compete = 400,
  ntarget_explore = 400,
  level_start = 1, 
  level_threshold = 0.75,
  level_targetl = level_targetl
  }


(*
fun write_targetl file targetl =
  let val tml = map dest_startboard targetl in
    export_terml (file ^ "_targetl") tml
  end
fun read_targetl file =
  let val tml = import_terml (file ^ "_targetl") in
    map mk_startboard tml
  end
*)

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val expname = "mleSetSynt-v2-1"

val rl_param =
  {
  expname = expname, 
  ex_window = 400, 
  ex_uniq = false, 
  ngen = 100,
  ncore_search = 8,
  ncore_train = 4}

val rl_preobj =
  {
  rl_param = rl_param,
  level_param = level_param,
  max_bigsteps = max_bigsteps,
  game = game,
  (* parallel search *)
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  (* dhtnn *)
  dhtnn_param = dhtnn_param,
  term_of_board = term_of_board
  }

val prl_search_es = mk_prl_search_es "mleSetSynt.prl_search_es" rl_preobj


(* -------------------------------------------------------------------------
   Reinforcement learning
   ------------------------------------------------------------------------- *)

(*
load "mleSetSynt"; open mleSetSynt;
(* export_setsyntdata (); *)
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mlReinforce"; open mlReinforce;
load "smlParallel"; open smlParallel;
load "aiLib"; open aiLib;

val rl_param =
  {
  expname = "test", 
  parallel_dir = smlParallel.parallel_dir ^ ,
  ntarget_compete : int, ntarget_explore : int,
  ex_window : int, ex_uniq : bool,
  ngen : int,
  level_start : int, level_threshold : real,
  level_targetl : int -> int -> 'a list,
  ncore_search : int, 
  par_search : (dhtnn, 'a, bool * 'a ex list) smlParallel.extspec,
  ncore_train : int


  }


val rl_preobj =

ncore_mcts_glob := 50;
ncore_train_glob := 4;
ntarget_level := 400;
ntarget_compete := 400;
ntarget_explore := 400;
exwindow_glob := 40000;
uniqex_flag := false;
dim_glob := 12;
graph_size := !dim_glob;
lr_glob := 0.02;
batchsize_glob := 16;
decay_glob := 0.99;
level_glob := 1;
nsim_glob := 16000;
nepoch_glob := 100;
ngen_glob := 100;
temp_flag := false;

logfile_glob := "aa_mleSetSynt11";
parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^ (!logfile_glob);
val r = start_rl_loop (gamespec,extspec);
*)

(* -------------------------------------------------------------------------
   Small test
   ------------------------------------------------------------------------- *)



(* -------------------------------------------------------------------------
   Example of interesting formulas
   ------------------------------------------------------------------------- *)

(* 
val formula = (funpow 20 random_step) start_form;
val formula = ``(qEXISTS_IN (vY0 :'a) (vX:'a) 
(oNOT (pEQ (vX:'a) (vY0 :'a):bool):bool):bool)``;
val formula = ``(qEXISTS_IN (vY0 :'a) (vX:'a) 
(oNOT (pSubq (vX:'a) ((tPower (vY0:'a)) :'a):bool):bool):bool)``;
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
      (term_size o dest_startboard) t) winl)
  in
    ((a,atot,int_div a atot), (b,btot, int_div b btot))
  end

fun final_eval fileout dhtnn set =
  let
    val l = test_compete test_eval_extspec dhtnn (map mk_startboard set)
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


(* -------------------------------------------------------------------------
   Test uniform search without guidance
   ------------------------------------------------------------------------- *)

fun search_uniform nsim tm =
  let 
    val _ = psMCTS.stopatwin_flag := true;
    val tree = mlReinforce.mcts_uniform nsim gamespec (mk_startboard tm);
    val r = 
      if can (psMCTS.trace_win (#status_of gamespec) tree) []
      then SOME (dlength tree) else NONE
    val _ = psMCTS.stopatwin_flag := false
  in
    r
  end

(* 
load "aiLib"; open aiLib;
load "mleSetLib"; open mleSetLib;
load "mlTacticData"; open mlTacticData;
load "mlReinforce"; open mlReinforce;
load "mleSetSynt"; open mleSetSynt;
val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt";
val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt");
val tml2 = first_n 100 tml1;
(* val (graphl,t) = add_time (map (mk_graph 64)) tml1; *)

val (tmnl,t) = add_time (map_assoc (search_uniform 16000)) tml2;
val tmnl_win = filter (isSome o snd) tmnl;
length tmnl_win;
*)



end (* struct *)
