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
   Program: 
     Address of buffer is 0.
     Addresses of inputs are 1 and 2.
     Additional addresses are 3 and 4.
  
   Only allowed to start grouping if used already many times.
   Not allowed to start grouping instruction before that.
   Grouping is good at it eliminates decay, reduce depth but enlarge 
   width. Only allowed to apply Cond or Loop on most frequent instruction.
   At each level add one new instruction to the language?
   ------------------------------------------------------------------------- *)

datatype move =
    Read of int 
  | Write of int
  | Incr of int 
  | Decr of int
  | Cond
  | Loop
  | EndLoop
  | EndCond


type program = move list

fun cond_block level acc prog = case prog of
    [] => raise ERR "cond_block" "open"
  | Cond :: m => cond_block (level + 1) (Cond :: acc) m
  | EndCond :: m => 
    if level <= 0 then (rev acc, m) else
      cond_block (level - 1) (EndCond :: acc) m
  | a :: m => cond_block level (a :: acc) m

fun loop_block level acc prog = case prog of
    [] => raise ERR "loop_block" "open"
  | Loop :: m => loop_block (level + 1) (Loop :: acc) m
  | EndLoop :: m => 
    if level <= 0 then (rev acc, m) else
      loop_block (level - 1) (EndLoop :: acc) m
  | a :: m => loop_block level (a :: acc) m

fun cond_blk p = cond_block 0 [] p
fun loop_blk p = loop_block 0 [] p

fun mk_blockl blockl prog = 
  let fun f instr m = mk_blockl ([instr] :: blockl) m in
    case prog of
    [] => rev blockl
  | Read i :: m  => f (Read i) m
  | Write i :: m => f (Write i) m
  | Incr i :: m  => f (Incr i) m
  | Decr i :: m  => f (Decr i) m
  | Cond :: m => 
    let 
      val (block,cont) = cond_blk m 
      val block' = (Cond :: block) @ [EndCond]
    in
      mk_blockl (block' :: blockl) cont
    end
  | Loop :: m =>
    let 
      val (block,cont) = loop_blk m 
      val block' = (Loop :: block) @ [EndLoop]
    in
      mk_blockl (block' :: blockl) cont
    end
  | _ => raise ERR "mk_blockl" ""
  end

fun exec_prog prog d = 
  case prog of
    [] => d
  | Read i :: m  => exec_prog m (dadd i (dfind 0 d) d)
  | Write i :: m => exec_prog m (dadd 0 (dfind i d) d)
  | Incr i :: m  => exec_prog m (dadd i ((dfind i d + 1) mod 8) d)
  | Decr i :: m  =>
    let val n = dfind i d in 
      if n > 0 then exec_prog m (dadd i (n-1) d) else exec_prog m d
    end
  | Cond :: m =>
    let
      val (block,cont) = cond_blk m
      val d' = if dfind 0 d <> 0 then exec_prog block d else d
    in
      exec_prog cont d'
    end
  | Loop :: m =>
    let 
      val (block,cont) = loop_blk m
      val d' = funpow (dfind 0 d) (exec_prog block) d
    in
      exec_prog cont d'
    end
  | _ => raise ERR "exec_prog" ""

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

type board = (int list * int) * (state list * program) * 
  (program * program * int)

fun mk_startsit (ol,limit) = 
  (true, ((ol,limit),(statel_org,[]),([],[],0)))

fun dest_startsit (_,(x,_,_)) = x

fun status_of (_,((ol,limit),(statel,p),_)) =
  if satisfies ol statel then Win 
  else if length p <= limit + 5 then Undecided
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

val condop = ``condop : bool -> bool``
fun mk_cond tm = mk_comb (condop,tm)
val loopop = ``loopop : bool -> bool``
fun mk_loop tm = mk_comb (loopop,tm)
val endcondop = ``endcondop : bool -> bool``
fun mk_endcond tm = mk_comb (endcondop,tm)
val endloopop = ``endloopop : bool -> bool``
fun mk_endloop tm = mk_comb (endloopop,tm)

fun nntm_of_instr ins tm = case ins of
    Read i  => mk_read (i, tm)
  | Write i => mk_write (i, tm)
  | Incr i  => mk_incr (i, tm)
  | Decr i  => mk_decr (i, tm)
  | Cond => mk_cond tm
  | Loop => mk_loop tm
  | EndCond => mk_endcond tm
  | EndLoop => mk_endloop tm

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
  [condop,loopop,endcondop,endloopop] @
  [isuc,izero,iconcat,sconcat,oconcat,joinop1,joinop2]
  )

fun nntm_of_sit (_,((ol,limit),(statel,p),_)) =
  mk_binop joinop2
    (mk_binop joinop1 (nntm_of_ol ol, nntm_of_statel statel),
     nntm_of_prog emptyop p)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

val varl_glob = List.tabulate (5,I)

val movel = List.concat
  [map Read (tl varl_glob), map Write (tl varl_glob),
   map Incr varl_glob, map Decr varl_glob,
   [Cond, Loop, EndCond, EndLoop]];

val moveil = number_snd 0 movel

fun move_compare (m1,m2) = 
  Int.compare (assoc m1 moveil, assoc m2 moveil)

fun string_of_move move = case move of
    Read i  => "R" ^ its i
  | Write i => "W" ^ its i
  | Incr i  => "I" ^ its i
  | Decr i  => "D" ^ its i
  | Cond => "C"
  | Loop => "L"
  | EndCond => "EC"
  | EndLoop => "EL"


fun is_possible (parl,n) m = case m of
    EndCond => ((hd parl = Cond) handle Empty => false)
  | EndLoop => ((hd parl = Loop) handle Empty => false)
  | Cond => null parl
  | Loop => null parl
  | _ => null parl orelse (n <= 1)

fun filter_sit (_,(_,(statel,_),(_,parl,n))) =
  let fun test (m,_) = is_possible (parl,n) m in fn l => filter test l end

fun apply_move move (_,((ol,limit),(statel,p),(b,parl,n))) = 
  if null parl then
    let 
      val _ = if not (null b) then raise ERR "apply_move" "" else ()
      val newp = p @ [move]
      fun f m = (map (exec_prog [m]) statel, ([],parl,n+1))
      fun g m = (statel, (b @ [m], m :: parl, n+1))
      val (newstatel,(newb,newparl,newn)) =  
      case move of
        Read i  => f move
      | Write i => f move
      | Incr i  => f move
      | Decr i  => f move
      | Cond => g move
      | Loop => g move
      | EndCond => raise ERR "apply_move" ""
      | EndLoop => raise ERR "apply_move" ""
    in
      (true,((ol,limit),(newstatel,newp),(newb,newparl,newn)))
    end 
  else  
    let
      val newp = p @ [move]
      fun f m = (statel, (b @ [m],parl,n+1))
      val (newstatel,(newb,newparl,newn)) =  
      case move of
        Read i  => f move
      | Write i => f move
      | Incr i  => f move
      | Decr i  => f move
      | Cond => (statel, (b @ [move], move :: parl, 0))
      | Loop => (statel, (b @ [move], move :: parl, 0))
      | EndCond =>
        if parl = [Cond]
        then (map (exec_prog (b @ [move])) statel, ([],[],0))
        else (statel, (b @ [move], tl parl,0))
      | EndLoop => 
        if parl = [Loop]
        then (map (exec_prog (b @ [move])) statel, ([],[],0))
        else (statel, (b @ [move], tl parl,0))
    in
      (true,((ol,limit),(newstatel,newp),(newb,newparl,newn)))
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

fun max_bigsteps (_,((_,limit),_,_)) = 2 * limit + 5

(* -------------------------------------------------------------------------
   Program generation
   ------------------------------------------------------------------------- *)

fun update_annot (parl,n) m = case m of
    EndCond => (tl parl, 0)
  | EndLoop => (tl parl, 0)
  | Cond => (m :: parl, 0)
  | Loop => (m :: parl, 0)
  | _ => (parl, n+1) 

fun is_possible_size size (parl,n) m = 
  let val size' = size - (length parl) in
    case m of
      EndCond => ((hd parl = Cond) handle Empty => false)
    | EndLoop => ((hd parl = Loop) handle Empty => false)
    | Cond => size' >= 2 andalso null parl
    | Loop => size' >= 2 andalso null parl
    | _ => size' > 0 andalso (null parl orelse (n <= 0))
  end

fun random_prog_aux size revp (parl,n) =
  if size <= 0 then rev (revp) else
  let 
    val movel' = filter (is_possible_size size (parl,n)) movel
    val move = random_elem movel'
    val newannot = update_annot (parl,n) move
  in
    random_prog_aux (size-1) (move :: revp) newannot
  end

fun random_prog size = random_prog_aux size [] ([],0)

(* -------------------------------------------------------------------------
   State generation
   ------------------------------------------------------------------------- *)

fun rand_olsize level = 
  let 
    val size = random_int (1,level)
    val p = random_prog size
    val ol = ol_of_statel (map (exec_prog p) statel_org)
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
  let val olsizel = gen_olsizel level in
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
val ol = map (fn [a,b] => 3) ill_glob;
val limit = 10;
fun extract_prog nodel = case #sit (hd nodel) of
  (_,(_,(_,p),_)) => p
val p = extract_prog (explore_gamespec (ol,limit));
*)

(*
load "mleProgram"; open mleProgram;
load "mlReinforce"; open mlReinforce;
load "smlParallel"; open smlParallel;
psMCTS.alpha_glob := 0.5;
logfile_glob := "program_run23";
parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^
(!logfile_glob);
ncore_mcts_glob := 4;
ncore_train_glob := 4;
ntarget_compete := 400;
ntarget_explore := 400;
exwindow_glob := 40000;
uniqex_flag := false;
dim_glob := 16;
lr_glob := 0.02;
batchsize_glob := 16;
decay_glob := 0.99;
level_glob := 10;
nsim_glob := 1600;
nepoch_glob := 100;
ngen_glob := 50;
start_rl_loop gamespec;
*)

end (* struct *)
