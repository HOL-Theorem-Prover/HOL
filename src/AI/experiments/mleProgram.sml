(* ========================================================================= *)
(* FILE          : mleProgram.sml                                            *)
(* DESCRIPTION   : Programming as a reinforcement learning game              *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleProgram :> mleProgram =
struct

open HolKernel boolLib Abbrev aiLib smlParallel psMCTS
  mlTreeNeuralNetwork mlReinforce

val ERR = mk_HOL_ERR "mleProgram"
fun debug s =
  debug_in_dir (HOLDIR ^ "/src/AI/experiments/debug") "mleProgram" s

(* -------------------------------------------------------------------------
   Program: Address of buffer is 0.
     Addresses of inputs are 1 and 2.
     Additional addresses are 3 and 4.
   ------------------------------------------------------------------------- *)

datatype instruction = 
    Read of int | Write of int
  | Incr of int | Decr of int

type program = instruction list

fun exec_instr instr d = 
  case instr of
    Read i  => dadd i (dfind 0 d) d
  | Write i => dadd 0 (dfind i d) d
  | Incr i  => dadd i (dfind i d + 1) d
  | Decr i  => 
    let val n = (dfind i d - 1) in
      if n <= 0 then d else dadd i (n-1) d
    end

(* -------------------------------------------------------------------------
   State
   ------------------------------------------------------------------------- *)

type state = (int,int) Redblackmap.dict

fun compare_statel (dl1,dl2) =
  list_compare (list_compare Int.compare)
    (map (map snd o dlist) dl1, map (map snd o dlist) dl2)

(* input *)
fun state_of_inputl il = 
  daddl (number_fst 1 il) (dnew Int.compare (List.tabulate (5,fn x => (x,0))))

val inputl_org =
  cartesian_productl [List.tabulate (3,I), List.tabulate (3,I)]

val statel_org = map state_of_inputl inputl_org

(* output *)
fun compare_ol (ol1,ol2) = list_compare Int.compare (ol1,ol2)
fun ol_of_statel statel = map (dfind 0) statel
fun satisfies ol statel = (compare_ol (ol_of_statel statel, ol) = EQUAL)
  
(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = 
  (int list * int) * 
  ((state list, unit) Redblackmap.dict * state list * program)

fun mk_startsit (ol,limit) = 
  (true, ((ol,limit), 
     (dadd statel_org () (dempty compare_statel), statel_org,[])))

fun dest_startsit (_,(x,_)) = x

fun status_of (_,((ol,limit),(_,statel,p))) =
  if satisfies ol statel then Win 
  else if length p <= 2 * limit then Undecided
  else Lose

(* -------------------------------------------------------------------------
   Representation of the program as a tree neural network
   ------------------------------------------------------------------------- *)

fun mk_varn n = mk_var ("x" ^ its n, bool)
val readop = ``readop : bool -> bool -> bool``
fun mk_read (i,tm) = list_mk_comb (readop,[mk_varn i,tm])
val writeop = ``writeop : bool -> bool -> bool``
fun mk_write (i,tm) = list_mk_comb (writeop,[mk_varn i,tm])
val incrop = ``incrop : bool -> bool -> bool``
fun mk_incr (i,tm) = list_mk_comb (incrop,[mk_varn i,tm])
val decrop = ``decrop : bool -> bool -> bool``
fun mk_decr (i,tm) = list_mk_comb (decrop,[mk_varn i,tm])
val emptyop = ``emptyop : bool``

fun nntm_of_instr ins tm = case ins of
    Read i  => mk_read (i, tm)
  | Write i => mk_write (i, tm)
  | Incr i  => mk_incr (i, tm)
  | Decr i  => mk_decr (i, tm)

fun nntm_of_prog acc p = case p of
    [] => acc 
  | ins :: m => nntm_of_prog (nntm_of_instr ins acc) m

(* -------------------------------------------------------------------------
   Representation of the state as a tree neural network
   ------------------------------------------------------------------------- *)

val isuc = ``isuc : bool -> bool``;
val izero = ``izero : bool``;
fun mk_isucn n =
  if n <= 0 then izero else mk_comb (isuc, mk_isucn (n-1))

val iconcat = ``iconcat : bool -> bool -> bool``
val sconcat = ``sconcat : bool -> bool -> bool``

fun list_mk_binop oper l = case l of
    [] => raise ERR "list_mk_binop" "empty list"
  | [a] => a
  | a :: m => mk_binop oper (a,list_mk_binop oper m)

fun nntm_of_state d = list_mk_binop iconcat (map (mk_isucn o snd) (dlist d))
fun nntm_of_statel dl = list_mk_binop sconcat (map nntm_of_state dl)   

(* -------------------------------------------------------------------------
   Representation of the desired outputs as a tree neural network
   ------------------------------------------------------------------------- *)

val oconcat = ``oconcat : bool -> bool -> bool``
fun nntm_of_ol ol = list_mk_binop oconcat (map mk_isucn ol)

(* -------------------------------------------------------------------------
   Representation of the board as a tree neural network
   ------------------------------------------------------------------------- *)

val joinop1 = ``joinop1 : bool -> bool -> bool``
val joinop2 = ``joinop2 : bool -> bool -> bool``

fun narg_oper oper = (length o fst o strip_type o type_of) oper

val program_operl =
  map_assoc narg_oper
  (
  List.tabulate (5,mk_varn) @ [readop,writeop,incrop,decrop,emptyop] @
  [isuc,izero,iconcat,sconcat,oconcat,joinop1,joinop2]
  )

fun nntm_of_sit (_,((ol,limit),(_,statel,prog))) =
  mk_binop joinop2
    (mk_binop joinop1 (nntm_of_ol ol, nntm_of_statel statel),
     nntm_of_prog emptyop prog)
(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

val varl_glob = List.tabulate (5,I)

datatype move = 
  ReadMove of int | WriteMove of int | 
  IncrMove of int | DecrMove of int

val movel = List.concat
  [map ReadMove (tl varl_glob), map WriteMove (tl varl_glob),
   map IncrMove varl_glob, map DecrMove varl_glob];

val moveil = number_snd 0 movel

fun apply_move_p move p =
  case move of
    ReadMove i  => p @ [Read i] 
  | WriteMove i => p @ [Write i]
  | IncrMove i  => p @ [Incr i]
  | DecrMove i  => p @ [Decr i]

fun apply_move_statel move dl =
  case move of
    ReadMove i  => map (exec_instr (Read i)) dl 
  | WriteMove i => map (exec_instr (Write i)) dl 
  | IncrMove i  => map (exec_instr (Incr i)) dl 
  | DecrMove i  => map (exec_instr (Decr i)) dl 

fun move_compare (m1,m2) = 
  Int.compare (assoc m1 moveil, assoc m2 moveil)

fun string_of_move move = case move of
    ReadMove i  => "R" ^ its i
  | WriteMove i => "W" ^ its i
  | IncrMove i  => "I" ^ its i
  | DecrMove i  => "D" ^ its i

fun filter_sit (_,(_,(hist,statel,_))) =
  let fun test (move,_) = 
    compare_statel (apply_move_statel move statel,statel) <> EQUAL 
  in
    fn l => filter test l
  end

fun apply_move move (_,((ol,limit),(hist,statel,p))) = 
  let val newstatel = apply_move_statel move statel in
  (true,
    ((ol,limit),
    (dadd newstatel () hist, newstatel, apply_move_p move p))
  )
  end

(* -------------------------------------------------------------------------
   Target
   ------------------------------------------------------------------------- *)

fun string_of_olsize (ol,limit) =
  its limit ^ "," ^ String.concatWith "," (map its ol)
fun write_targetl targetl =
  let val olsizel = map dest_startsit targetl in
    writel (!parallel_dir ^ "/targetl") (map string_of_olsize olsizel)
  end

fun olsize_from_string s = case String.tokens (fn c => c = #",") s of
    [] => raise ERR "olsize_from_string" ""
  | a :: m => (map string_to_int m, string_to_int a)
fun read_targetl () =
  let val sl = readl (!parallel_dir ^ "/targetl") in
    map (mk_startsit o olsize_from_string) sl
  end

fun max_bigsteps (_,((_,limit),_)) = 2 * limit + 5

(* -------------------------------------------------------------------------
   Program generation
   ------------------------------------------------------------------------- *)

fun gen_prog_movel ml p = case ml of
    [] => p
  | move :: m => gen_prog_movel m (apply_move_p move p)
  
fun random_prog size = 
  gen_prog_movel (List.tabulate (size, fn _ => random_elem movel)) []

(* -------------------------------------------------------------------------
   State generation
   ------------------------------------------------------------------------- *)

fun next_level (hist,statell) =
  let 
    val statell1 = 
      map (uncurry apply_move_statel) (cartesian_product movel statell)
    val statell2 = mk_fast_set compare_statel statell1
    val statell3 = filter (fn x => not (dmem x hist)) statell2  
  in
    (daddl (map_assoc (fn x => ()) statell3) hist,
     statell3)
  end

fun all_level (i,level) x =
  if i >= level then [(i,snd x)] else 
    (i,snd x) :: all_level (i+1,level) (next_level x)

(*
fun gen_olsizel level =
  let
    val hist = dadd statel_org () (dempty compare_statel)
    val l1 = tl (all_level (0,level) (hist,[statel_org]))
    val l2 = distrib l1
    val l3 = map_snd ol_of_statel l2
    val l4 = map swap l3
    val d4 = dregroup compare_ol l4
  in
    map_snd list_imin (dlist d4)
  end
*)

fun rand_olsize level = 
  let 
    val size = random_int (1,level)
    val ml = List.tabulate (size,fn _ => random_elem movel) 
    fun loop l statel = case l of 
      [] => statel
    | a :: m => loop m (apply_move_statel a statel) 
    val ol = ol_of_statel (loop ml statel_org)
  in
    (ol,size)
  end

fun gen_olsizel level =
  let val olsizel = List.tabulate (100000, fn _ => rand_olsize level) in
    map_snd list_imin (dlist (dregroup compare_ol olsizel))
  end

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

fun mk_targetl level ntarget =
  let val olsizel = gen_olsizel (level * 10) in
    map mk_startsit (first_n ntarget (shuffle olsizel))
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
  operl = program_operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  opens = "mleProgram",
  max_bigsteps = max_bigsteps
  }

(* -------------------------------------------------------------------------
   Basic exploration
   ------------------------------------------------------------------------- *)

fun explore_gamespec (ol,limit) =
  let val dhtnn = random_dhtnn_gamespec gamespec in
    explore_test gamespec dhtnn (mk_startsit (ol,limit))
  end

(*
load "mleProgram"; open mleProgram;
load "aiLib"; open aiLib;

mlReinforce.nsim_glob := 1600;
val ill_glob =
  map list_of_pair
  (cartesian_product (List.tabulate (3,I)) (List.tabulate (3,I)));
val ol = map (fn [a,b] => a+4) ill_glob;
val limit = 10;
explore_gamespec (ol,limit);
*)

(*
load "mleProgram"; open mleProgram;
load "mlReinforce"; open mlReinforce;
load "smlParallel"; open smlParallel;
psMCTS.alpha_glob := 0.5;
logfile_glob := "program_run22";
parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^
(!logfile_glob);
ncore_mcts_glob := 16;
ncore_train_glob := 16;
ntarget_compete := 400;
ntarget_explore := 400;
exwindow_glob := 40000;
uniqex_flag := false;
dim_glob := 16;
lr_glob := 0.02;
batchsize_glob := 16;
decay_glob := 0.99;
level_glob := 2;
nsim_glob := 1600;
nepoch_glob := 100;
ngen_glob := 50;
start_rl_loop gamespec;
*)

end (* struct *)
