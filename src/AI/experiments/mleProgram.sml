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

type iol = (int list * int) list

(* -------------------------------------------------------------------------
   Program
   ------------------------------------------------------------------------- *)

datatype program =
  Read of (int * program) |
  Write of (int * program) |
  Incr of (int * program) |
  Reset of (int * program) |
  Loop of ((int * program) * program) |
  End |
  Cont

exception ProgTimeout

fun exec_prog t p d =
  if t <= 0 then raise ProgTimeout else
  case p of
    Read (i,p1)  => exec_prog (t-1) p1 (dadd i (dfind 0 d) d)
  | Write (i,p1) => exec_prog (t-1) p1 (dadd 0 (dfind i d) d)
  | Incr (i,p1)  => exec_prog (t-1) p1 (dadd i (dfind i d + 1) d)
  | Reset (i,p1) => exec_prog (t-1) p1 (dadd i 0 d)
  | Loop ((i,p1),p2) =>
    (
    if dfind i d <= 0 then exec_prog (t-1) p2 d else
      let
        val (d1,tp1) = exec_prog t p1 d
        val d2 = dadd i (dfind i d - 1) d1
      in
        exec_prog (tp1-1) p d2
      end
    )
  | End => (d:(int, int) Redblackmap.dict,t)
  | Cont => raise ERR "exec_prog" "cont"

fun exec_prog_onlist p l =
  let
    val d0 = dnew Int.compare (List.tabulate (8,fn x => (x,0)))
    val d1 = daddl (number_fst 1 l) d0
  in
    dfind 0 (fst (exec_prog 1000 p d1))
  end
   handle ProgTimeout => 0 | NotFound => 0

fun satisifies p (il,i) = (i = exec_prog_onlist p il)
fun satisfies_iol p l = all (satisifies p) l

fun contains_cont p = case p of
    Read (i,p1)  => contains_cont p1
  | Write (i,p1) => contains_cont p1
  | Incr (i,p1)  => contains_cont p1
  | Reset (i,p1) => contains_cont p1
  | Loop ((i,p1),p2) => contains_cont p1 orelse contains_cont p2
  | End => false
  | Cont => true


fun prog_size p = case p of
    Read (i,p1)  => 1 + i + prog_size p1
  | Write (i,p1) => 1 + i + prog_size p1
  | Incr (i,p1)  => 1 + i + prog_size p1
  | Reset (i,p1) => 1 + i + prog_size p1
  | Loop ((i,p1),p2) => 1 + i + prog_size p1 + prog_size p2
  | End => 1
  | Cont => 1

(*
val p = Read(1,Loop((2,Incr(0,End)),End));
val addin = let val l = List.tabulate (10,I) in cartesian_product l l end;
val addinout = map_assoc (op +) addin;
*)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

datatype board =
  Board of ((int list * int) list * int * program) | FailBoard

fun mk_startsit (iol,size) = (true, Board (iol,size,Cont))
fun dest_startsit target = case target of
    (true, Board (iol,size,Cont)) => (iol,size)
  | _ => raise ERR "dest_startsit" ""

fun status_of sit = case snd sit of
    Board (iol,size,p) =>
      if prog_size p > 2 * size then Lose
      else if contains_cont p then Undecided
      else if satisfies_iol p iol then Win else Lose (* maybe cache this *)
  | FailBoard => Lose

(* -------------------------------------------------------------------------
   Neural network units and inputs
   ------------------------------------------------------------------------- *)

val boolsuc = ``boolsuc : bool -> bool``;
val boolzero = ``boolzero : bool``;
fun mk_boolsucn n =
  if n <= 0 then boolzero else mk_comb (boolsuc, mk_boolsucn (n-1))

val readop = ``readop : bool -> bool -> bool``;
fun mk_readop (t1,t2) = list_mk_comb (readop,[t1,t2]);

val writeop = ``writeop : bool -> bool -> bool``;
fun mk_writeop (t1,t2) = list_mk_comb (writeop,[t1,t2]);

val incrop = ``incrop : bool -> bool -> bool``;
fun mk_incrop (t1,t2) = list_mk_comb (incrop,[t1,t2]);

val resetop = ``resetop : bool -> bool -> bool``;
fun mk_resetop (t1,t2) = list_mk_comb (resetop,[t1,t2]);

val loopop = ``loopop : bool -> bool -> bool -> bool``;
fun mk_loopop (t1,t2,t3) = list_mk_comb (loopop,[t1,t2,t3]);

val endop = ``endop : bool``;
val contop = ``contop : bool``;

fun nntm_of_prog p = case p of
    Read (i,p1)  => mk_readop (mk_boolsucn i, nntm_of_prog p1)
  | Write (i,p1) => mk_writeop (mk_boolsucn i, nntm_of_prog p1)
  | Incr (i,p1)  => mk_incrop (mk_boolsucn i, nntm_of_prog p1)
  | Reset (i,p1) => mk_resetop (mk_boolsucn i, nntm_of_prog p1)
  | Loop ((i,p1),p2) =>
    mk_loopop (mk_boolsucn i, nntm_of_prog p1, nntm_of_prog p2)
  | End => endop
  | Cont => contop

val isuc = ``isuc : bool -> bool``;
val izero = ``izero : bool``;
fun mk_isucn n =
  if n <= 0 then izero else mk_comb (isuc, mk_isucn (n-1))
val iconcat = ``iconcat : bool -> bool -> bool``
fun mk_iconcat (a,b) = list_mk_comb (iconcat,[a,b])
fun list_mk_iconcat al = case al of
    [] => raise ERR "list_mk_iconcat" "empty list"
  | [a] => a
  | a :: m => mk_iconcat (a,list_mk_iconcat m)
val iojoin = ``iojoin : bool -> bool -> bool``
fun mk_iojoin (a,b) = list_mk_comb (iojoin,[a,b])
val ioconcat = ``ioconcat : bool -> bool -> bool``
fun mk_ioconcat (a,b) = list_mk_comb (ioconcat,[a,b])
fun list_mk_ioconcat al = case al of
    [] => raise ERR "list_mk_ioconcat" "empty list"
  | [a] => a
  | a :: m => mk_ioconcat (a,list_mk_ioconcat m)
fun nntm_of_il il = list_mk_iconcat (map mk_isucn il)
fun nntm_of_io (il,i) = mk_iojoin (nntm_of_il il,mk_isucn i)
fun nntm_of_iol iol = list_mk_ioconcat (map nntm_of_io iol)

val iopjoin = ``iopjoin : bool -> bool -> bool``
fun mk_iopjoin (a,b) = list_mk_comb (iopjoin,[a,b])
fun nntm_of_sit sit = case snd sit of
    Board (iol,size,p) => mk_iopjoin (nntm_of_iol iol, nntm_of_prog p)
  | FailBoard => T


fun narg_oper oper = (length o fst o strip_type o type_of) oper

val program_operl =
  map_assoc narg_oper
  (
  [boolsuc,boolzero,readop,writeop,incrop,resetop,loopop,endop,contop] @
  [isuc,izero,iconcat,iojoin,ioconcat,iopjoin]
  )

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move =
  AddrMove | ReadMove | WriteMove | IncrMove | ResetMove | LoopMove | EndMove

val movel = [AddrMove,ReadMove,WriteMove,IncrMove,ResetMove,LoopMove,EndMove];
val moveil = number_snd 0 movel

fun apply_othermove move p = case p of
    Read (i,p1)  => Read (i,apply_othermove move p1)
  | Write (i,p1) => Write (i,apply_othermove move p1)
  | Incr (i,p1)  => Incr (i,apply_othermove move p1)
  | Reset (i,p1) => Reset (i,apply_othermove move p1)
  | Loop ((i,p1),p2) =>
    let val p1' = apply_othermove move p1 in
      if p1 <> p1'
      then Loop ((i,p1'),p2)
      else Loop ((i,p1),apply_othermove move p2)
    end
  | End => End
  | Cont => (case move of
      AddrMove  => raise ERR "addrmove" ""
    | ReadMove  => Read (1,Cont)
    | WriteMove => Write (1,Cont)
    | IncrMove  => Incr (1,Cont)
    | ResetMove => Reset (1,Cont)
    | LoopMove  => Loop ((1,Cont),Cont)
    | EndMove   => End
    )

exception AddrException

fun apply_addrmove p = case p of
    Read (i,Cont)  => Read (i+1,Cont)
  | Write (i,Cont) => Write (i+1,Cont)
  | Incr (i,Cont)  => Incr (i+1,Cont)
  | Reset (i,Cont) => Reset (i+1,Cont)
  | Loop ((i,Cont),p2) => Loop ((i+1,Cont),p2)
  | Read (i,p1)  => Read (i,apply_addrmove p1)
  | Write (i,p1) => Write (i,apply_addrmove p1)
  | Incr (i,p1)  => Incr (i,apply_addrmove p1)
  | Reset (i,p1) => Reset (i,apply_addrmove p1)
  | Loop ((i,p1),p2) =>
    let val p1' = apply_addrmove p1 in
      if p1 <> p1'
      then Loop ((i,p1'),p2)
      else Loop ((i,p1),apply_addrmove p2)
    end
  | End => End
  | Cont => raise AddrException

fun move_compare (m1,m2) = Int.compare (assoc m1 moveil, assoc m2 moveil)

fun string_of_move move = case move of
    AddrMove => "A"
  | ReadMove => "R"
  | WriteMove => "W"
  | IncrMove => "I"
  | ResetMove => "S"
  | LoopMove => "L"
  | EndMove => "E"

fun filter_sit sit = case snd sit of
    Board _ => (fn l => l)
  | FailBoard => (fn l => [])

fun apply_move move sit =
  (true,
    case snd sit of
      Board (iol,size,p) =>
        Board (iol,size,
        if move = AddrMove then apply_addrmove p else apply_othermove move p)
    | FailBoard => raise ERR "apply_move" ""
  )
  handle AddrException => (true, FailBoard)

(* -------------------------------------------------------------------------
   Target
   ------------------------------------------------------------------------- *)

fun string_of_io (il,i) = String.concatWith " " (its i :: map its il)
fun string_of_iolsize (iol,size) =
  its size ^ "," ^ String.concatWith "," (map string_of_io iol)
fun write_targetl targetl =
  let val iolsizel = map dest_startsit targetl in
    writel (!parallel_dir ^ "/targetl") (map string_of_iolsize iolsizel)
  end

fun io_from_string s = case String.tokens Char.isSpace s of
    [] => raise ERR "io_from_string" ""
  | a :: m => (map string_to_int m, string_to_int a)
fun iolsize_from_string s = case String.tokens (fn c => c = #",") s of
    [] => raise ERR "iolsize_from_string" ""
  | a :: m => (map io_from_string m, string_to_int a)
fun read_targetl () =
  let
    val sl = readl (!parallel_dir ^ "/targetl")
    val iolsizel = map iolsize_from_string sl
  in
    map mk_startsit iolsizel
  end

fun max_bigsteps target = case snd target of
    Board (_,size,_) => 2 * size + 1
  | FailBoard => raise ERR "max_bigsteps" ""

(* -------------------------------------------------------------------------
   Level: uses program generation (semantic uniqueness)
   ------------------------------------------------------------------------- *)

fun int_product nl = case nl of
    [] => 1
  | a :: m => a * int_product m

fun number_partition_err a b =
  number_partition a b handle HOL_ERR _ => []

val instrl =
  [Read (0,End), Write (0,End), Incr (0,End), Reset (0,End),
   Loop ((0,End),End), End]

val gen_cache = ref (dempty Int.compare)

fun gen_prog size =
  (dfind size (!gen_cache) handle NotFound =>
  let val value = List.concat (map (gen_prog_instr size) instrl) in
    gen_cache := dadd size value (!gen_cache);
    value
  end)
and gen_prog_instr size instr = case instr of
    Read (_,_)  => gen_prog_pair Read size
  | Write (_,_) => gen_prog_pair Write size
  | Incr (_,_)  => gen_prog_pair Incr size
  | Reset (_,_) => gen_prog_pair Reset size
  | Loop ((_,_),_) =>
    let
      val l = map triple_of_list (number_partition_err 3 size)
      fun f (a,b,c) =
        let val l' = cartesian_product (gen_prog b) (gen_prog c) in
          map (fn (b',c') => Loop ((a,b'),c')) l'
        end
    in
      List.concat (map f l)
    end
  | End => if size = 1 then [End] else []
  | Cont => raise ERR "exec_prog" "cont"
and gen_prog_pair constructor size =
  let
    val l = map pair_of_list (number_partition_err 2 size)
    fun f (a,b) = map (fn x => constructor (a,x)) (gen_prog b)
  in
    List.concat (map f l)
  end

val n_cache = ref (dempty Int.compare)

fun n_prog size =
  (dfind size (!n_cache) handle NotFound =>
  let val value = sum_int (map (n_prog_instr size) instrl) in
    n_cache := dadd size value (!n_cache);
    value
  end)
and n_prog_instr size instr = case instr of
    Read (_,_)  => n_prog_pair Read size
  | Write (_,_) => n_prog_pair Write size
  | Incr (_,_)  => n_prog_pair Incr size
  | Reset (_,_) => n_prog_pair Reset size
  | Loop ((_,_),_) =>
    let
      val l = map triple_of_list (number_partition_err 3 size)
      fun f (a,b,c) = n_prog b * n_prog c
    in
      sum_int (map f l)
    end
  | End => if size = 1 then 1 else 0
  | Cont => raise ERR "n_prog" "cont"
and n_prog_pair constructor size =
  let
    val l = map pair_of_list (number_partition_err 2 size)
    fun f (a,b) = n_prog b
  in
    sum_int (map f l)
  end

fun random_prog size =
  if n_prog size <= 0 then raise ERR "random_prog" "" else
  let
    val freql1 = map_assoc (n_prog_instr size) instrl
    val freql2 = filter (fn x => snd x > 0) freql1
    val freql3 = map_snd Real.fromInt freql2
  in
    random_prog_instr size (select_in_distrib freql3)
  end
and random_prog_instr size instr = case instr of
    Read (_,_)  => random_prog_pair Read size
  | Write (_,_) => random_prog_pair Write size
  | Incr (_,_)  => random_prog_pair Incr size
  | Reset (_,_) => random_prog_pair Reset size
  | Loop ((_,_),_) =>
    let
      val l = map triple_of_list (number_partition_err 3 size)
      fun f (a,b,c) = n_prog b * n_prog c
      val freql1 = map_assoc f l
      val freql2 = filter (fn x => snd x > 0) freql1
      val freql3 = map_snd Real.fromInt freql2
      val (achosen,bchosen,cchosen) = select_in_distrib freql3
    in
      Loop ((achosen,random_prog bchosen),random_prog cchosen)
    end
  | End => if size = 1 then End else raise ERR "random_prog" "end"
  | Cont => raise ERR "random_prog" "cont"
and random_prog_pair constructor size =
  let
    val l = map pair_of_list (number_partition_err 2 size)
    fun f (a,b) = n_prog b
    val freql1 = map_assoc f l
    val freql2 = filter (fn x => snd x > 0) freql1
    val freql3 = map_snd Real.fromInt freql2
    val (achosen,bchosen) = select_in_distrib freql3
  in
    constructor (achosen,random_prog bchosen)
  end

fun compare_iol (iol1,iol2) =
  let
    val iol1' = map (fn (il,i) => i :: il) iol1
    val iol2' = map (fn (il,i) => i :: il) iol2
  in
    list_compare (list_compare Int.compare) (iol1',iol2')
  end

val ill_glob =
  map list_of_pair
  (cartesian_product (List.tabulate (4,I)) (List.tabulate (4,I)));

fun iol_of_prog p = map_assoc (exec_prog_onlist p) ill_glob

val targetlevel_cache = ref (dempty Int.compare)

fun list_imin l = case l of
    [] => raise ERR "list_imin" ""
  | [a] => a
  | a :: m => Int.min (a,list_imin m)

fun mk_targetl level ntarget =
  let
    val iolset =
      dfind level (!targetlevel_cache) handle NotFound =>
      let
        val pl = List.concat (List.tabulate (level,gen_prog))
        val iolsizel = map_snd prog_size (map swap (map_assoc iol_of_prog pl))
        fun f (k,vl) = list_imin vl
      in
        dlist (dmap f (dregroup compare_iol iolsizel))
      end
  in
    targetlevel_cache := dadd level iolset (!targetlevel_cache);
    map mk_startsit (first_n ntarget (shuffle iolset))
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

fun explore_gamespec (iol,size) =
  let val dhtnn = random_dhtnn_gamespec gamespec in
    explore_test gamespec dhtnn (mk_startsit (iol,size))
  end

(*
load "mleProgram"; open mleProgram;
load "aiLib"; open aiLib;

mlReinforce.nsim_glob := 1600;
val ill_glob =
  map list_of_pair
  (cartesian_product (List.tabulate (3,I)) (List.tabulate (3,I)));
val iol = map_assoc (fn [a,b] => a+b) ill_glob;
val size = 10;
explore_gamespec (iol,size);

load "mleProgram"; open mleProgram;
psMCTS.alpha_glob := 0.2;
reinforce_fixed "program_run3" 20;
*)

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
  level_glob := 9;
  nsim_glob := 1600;
  nepoch_glob := 100;
  ngen_glob := ngen;
  start_rl_loop gamespec
  )

end (* struct *)
