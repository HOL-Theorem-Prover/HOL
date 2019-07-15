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

(* -------------------------------------------------------------------------
   Program: Address of buffer is 0.
   Addresses of inputs are 1 and 2.
   Additional addresses are 3 and 4.
   ------------------------------------------------------------------------- *)

datatype move =
    Read of int | Write of int
  | Incr of int | Decr of int
  | Cond | Loop
  | EndLoop | EndCond
  | Macro of int

fun string_of_move move = case move of
    Read i => "R" ^ its i
  | Write i => "W" ^ its i
  | Incr i => "I" ^ its i
  | Decr i => "D" ^ its i
  | Cond => "C"
  | Loop => "L"
  | EndCond => "EC"
  | EndLoop => "EL"
  | Macro i => "M" ^ its i

val max_macro = 20
val max_register = 5
val macro_array = 
  ref (Vector.fromList (List.tabulate (max_macro, fn _ => NONE)))

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

exception ProgTimeout

fun exec_prog_aux prog (d,t) = 
  if t <= 0 then raise ProgTimeout else
  case prog of
    [] => (d,t)
  | Read i :: m  => exec_prog_aux m (dadd i (dfind 0 d) d, t-1)
  | Write i :: m => exec_prog_aux m (dadd 0 (dfind i d) d, t-1)
  | Incr i :: m  => exec_prog_aux m (dadd i ((dfind i d + 1) mod 8) d, t-1)
  | Decr i :: m  =>
    let val n = dfind i d in 
      if n > 0 
      then exec_prog_aux m (dadd i (n-1) d, t-1) 
      else exec_prog_aux m (d,t-1)
    end
  | Cond :: m =>
    let
      val (block,cont) = cond_blk m
      val (d',t') = if dfind 0 d <> 0 then exec_prog_aux block (d,t) else (d,t)
    in
      exec_prog_aux cont (d',t'-1)
    end
  | Loop :: m =>
    let 
      val (block,cont) = loop_blk m
      val (d',t') = funpow (dfind 0 d) (exec_prog_aux block) (d,t)
    in
      exec_prog_aux cont (d',t'-1)
    end
  | _ => raise ERR "exec_prog_aux" ""

fun exec_prog p d = (fst (exec_prog_aux p (d,1000)) handle ProgTimeout => d)

fun parl_of_prog p parl = 
  case p of
    [] => parl
  | Cond :: m => parl_of_prog m (Cond :: parl)
  | Loop :: m => parl_of_prog m (Loop :: parl)
  | EndCond :: m => parl_of_prog m (tl parl)
  | EndLoop :: m => parl_of_prog m (tl parl)
  | a :: m => parl_of_prog m parl

fun lastblock_of_prog p (acc1,acc2) parl =
   case p of
    [] => (acc1,acc2)
  | Cond :: m => 
    if null parl 
    then lastblock_of_prog m (acc1, [Cond]) (Cond :: parl) 
    else lastblock_of_prog m (acc1, acc2 @ [Cond]) (Cond :: parl)
  | Loop :: m => 
    if null parl 
    then lastblock_of_prog m (acc1, [Loop]) (Loop :: parl) 
    else lastblock_of_prog m (acc1, acc2 @ [Loop]) (Loop :: parl)
  | EndCond :: m => 
    if parl = [Cond] 
    then lastblock_of_prog m (acc1 @ acc2 @ [EndCond], []) (tl parl) 
    else lastblock_of_prog m (acc1, acc2 @ [EndCond]) (tl parl)
  | EndLoop :: m => 
    if parl = [Loop] 
    then lastblock_of_prog m (acc1 @ acc2 @ [EndLoop], []) (tl parl) 
    else lastblock_of_prog m (acc1, acc2 @ [EndLoop]) (tl parl)
  | a :: m =>
    if null parl 
    then lastblock_of_prog m (acc1 @ [a], []) parl 
    else lastblock_of_prog m (acc1, acc2 @ [a]) parl

(* -------------------------------------------------------------------------
   State
   ------------------------------------------------------------------------- *)

type state = (int,int) Redblackmap.dict

fun compare_statel (dl1,dl2) =
  list_compare (list_compare Int.compare)
    (map (map snd o dlist) dl1, map (map snd o dlist) dl2)

(* input *)
fun state_of_inputl il = 
  daddl (number_fst 1 il) 
    (dnew Int.compare (List.tabulate (max_register,fn x => (x,0))))

val inputl_org = cartesian_productl [List.tabulate (3,I), List.tabulate (3,I)]
val statel_org = map state_of_inputl inputl_org

(* output *)
fun compare_ol (ol1,ol2) = list_compare Int.compare (ol1,ol2)
fun ol_of_statel statel = map (dfind 0) statel
fun satisfies ol statel = (compare_ol (ol_of_statel statel, ol) = EQUAL)
  
(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (int list * int) * (state list * program) * (program * program)

fun mk_startsit (ol,(p,limit)) = 
  let
    val (p',b) = lastblock_of_prog p ([],[]) []
    val _ = print_endline (String.concatWith " " (map string_of_move p'))
    val statel = map (exec_prog p') statel_org
    val parl = parl_of_prog p []
  in
    ((ol,limit),(statel,p),(b,parl))
  end

fun dest_startsit ((ol,limit),(statel,p),_) = (ol,(p,limit))

fun status_of ((ol,limit),(statel,p),_) =
  if satisfies ol statel then Win 
  else if length p <= limit then Undecided
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

fun mk_macron i = mk_var ("m" ^ its i, ``: bool -> bool``)
fun mk_macro (i,tm) = mk_comb (mk_macron i,tm)

fun nntm_of_instr ins tm = case ins of
    Read i  => mk_read (i,tm)
  | Write i => mk_write (i,tm)
  | Incr i  => mk_incr (i,tm)
  | Decr i  => mk_decr (i,tm)
  | Cond => mk_cond tm
  | Loop => mk_loop tm
  | EndCond => mk_endcond tm
  | EndLoop => mk_endloop tm
  | Macro i => mk_macro (i,tm)

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
  List.tabulate (max_register,mk_varn) @
  [readop,writeop,incrop,decrop,emptyop] @
  [condop,loopop,endcondop,endloopop] @
  [isuc,izero,iconcat,sconcat,oconcat,joinop1,joinop2] @
  List.tabulate (max_macro,mk_macron)
  )

fun nntm_of_sit ((ol,limit),(statel,p),_) =
  mk_binop joinop2 (nntm_of_ol ol, nntm_of_prog emptyop p)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

val varl_glob = List.tabulate (max_register,I)

val movel = 
  List.concat
  [map Read (tl varl_glob), map Write (tl varl_glob),
   map Incr varl_glob, map Decr varl_glob,
   [Cond, Loop, EndCond, EndLoop]]

val movel_ext = movel @ map Macro (List.tabulate (max_macro,I))

fun move_compare (m1,m2) = 
  String.compare (string_of_move m1, string_of_move m2) 

fun apply_move move ((ol,limit),(statel,p),(b,parl)) = 
  if null parl then
    let 
      val _ = if not (null b) then raise ERR "apply_move" "" else ()
      val newp = p @ [move]
      fun f m = (map (exec_prog [m]) statel, ([],parl))
      fun g m = (statel, (b @ [m], m :: parl))
      val (newstatel,(newb,newparl)) =  
      case move of
        Read i  => f move
      | Write i => f move
      | Incr i  => f move
      | Decr i  => f move
      | Cond => g move
      | Loop => g move
      | EndCond => raise ERR "apply_move" ""
      | EndLoop => raise ERR "apply_move" ""
      | _ => raise ERR "apply_move" "macro"
    in
      ((ol,limit),(newstatel,newp),(newb,newparl))
    end 
  else  
    let
      val newp = p @ [move]
      fun f m = (statel, (b @ [m],parl))
      val (newstatel,(newb,newparl)) =  
      case move of
        Read i  => f move
      | Write i => f move
      | Incr i  => f move
      | Decr i  => f move
      | Cond => (statel, (b @ [move], move :: parl))
      | Loop => (statel, (b @ [move], move :: parl))
      | EndCond =>
        if hd parl <> Cond then raise ERR "apply_move" "" else
        if parl = [Cond]
        then (map (exec_prog (b @ [move])) statel, ([],[]))
        else (statel, (b @ [move], tl parl))
      | EndLoop => 
        if hd parl <> Loop then raise ERR "apply_move" "" else
        if parl = [Loop]
        then (map (exec_prog (b @ [move])) statel, ([],[]))
        else (statel, (b @ [move], tl parl)) 
      | _ => raise ERR "apply_move" "macro"
    in
      ((ol,limit),(newstatel,newp),(newb,newparl))
    end

fun apply_move_ext move sit = case move of
    Macro i => 
    let 
      val ((ol,limit),(statel,p),(newb,newparl)) = sit
      val ml = valOf (Vector.sub (!macro_array,i)) 
      val (_,(newstatel,_),(newb,newparl)) =
        foldl (uncurry apply_move) sit ml
    in
      ((ol,limit),(newstatel,p @ [move]),(newb,newparl))
    end
  | _ => apply_move move sit 

fun filter_sit sit =
  let fun test (m,_) = can (apply_move m) sit in fn l => filter test l end

(* -------------------------------------------------------------------------
   Target
   ------------------------------------------------------------------------- *)

fun string_of_macro ml = case ml of
   NONE => "NONE"
 | SOME ml' => "SOME," ^ String.concatWith "," (map string_of_move ml') 

fun string_of_olsize (ol,(p,limit)) =
  its limit ^ "," ^ String.concatWith "," (map its ol) ^ "#" ^
  String.concatWith "," (map string_of_move p)

fun write_targetl file targetl =
  let 
    val macrol = vector_to_list (!macro_array)
    val olsizel = map dest_startsit targetl 
  in
    writel (file ^ "_macrol") (map string_of_macro macrol);
    writel (file ^ "_targetl") (map string_of_olsize olsizel)
  end

fun olsize_from_string s = 
  case String.tokens (fn c => c = #",") s of
    [] => raise ERR "olsize_from_string" ""
  | a :: m => (map string_to_int m, string_to_int a)

fun index_of_smove s = 
  string_to_int (implode (tl (explode s)))

fun move_from_string s = case s of
    "C" => Cond
  | "L" => Loop
  | "EC" => EndCond
  | "EL" => EndLoop
  | _ =>
    (
    case String.sub (s,0) of
      #"R" => Read (index_of_smove s)
    | #"W" => Write (index_of_smove s)
    | #"I" => Incr (index_of_smove s)
    | #"D" => Decr (index_of_smove s)
    | #"M" => Macro (index_of_smove s)
    | _ => raise ERR "move_from_string" ""
    )
   
fun prog_from_string s =
  map move_from_string (String.tokens (fn c => c = #",") s)

fun macro_from_string s = case String.tokens (fn c => c = #",") s of
    ["NONE"]    => NONE
  | "SOME" :: m => SOME (map move_from_string m)
  | _           => raise ERR "macro_from_string" ""

fun olpsize_from_string s = 
  let 
    val (sa,sb) = pair_of_list (String.fields (fn c => c = #"#") s) 
    val (ol,psize) = olsize_from_string sa
    val p = prog_from_string sb
  in
    (ol,(p,psize))
  end

fun read_targetl file =
  let 
    val macrol = map macro_from_string (readl (file ^ "_macrol"))
    val sl = readl (file ^ "_targetl")
  in
    macro_array := Vector.fromList macrol;
    map (mk_startsit o olpsize_from_string) sl
  end

fun max_bigsteps ((_,limit),_,_) = limit + 1

(* -------------------------------------------------------------------------
   Program generation
   ------------------------------------------------------------------------- *)

fun update_annot (parl,n) m = case m of
    EndCond => (tl parl, 0)
  | EndLoop => (tl parl, 0)
  | Cond => (m :: parl, 0)
  | Loop => (m :: parl, 0)
  | _ => (parl, n+1) 

val level_parameters = ref []

fun is_possible_param (psize,ctrln,ctrlsize,nestn) (parl,n) m = 
  let val psize' = psize - (length parl) in
    case m of
      EndCond => ((hd parl = Cond) handle Empty => false)
    | EndLoop => ((hd parl = Loop) handle Empty => false)
    | Cond => psize' >= 2 andalso length parl <= nestn andalso ctrln > 0
    | Loop => psize' >= 2 andalso length parl <= nestn andalso ctrln > 0
    | _ => psize' > 0 andalso (null parl orelse n < ctrlsize)
  end

fun update_param (psize,ctrln,ctrlsize,nestn) m = 
  (psize-1, if mem m [Cond,Loop] then ctrln-1 else ctrln, 
   ctrlsize,
   nestn)

fun random_prog_aux (param as (psize,ctrln,ctrlsize,nestn)) revp (parl,n) =
  if psize <= 0 then rev (revp) else
  let
    val movel' = filter (is_possible_param param (parl,n)) movel
    val move = random_elem movel'
    val newannot = update_annot (parl,n) move
    val newparam = update_param param move
  in
    random_prog_aux newparam (move :: revp) newannot
  end

fun random_prog param = random_prog_aux param [] ([],0)

(* -------------------------------------------------------------------------
   State generation
   ------------------------------------------------------------------------- *)

fun rand_olsize level = 
  let 
    val (a,b,c,d) = List.nth (!level_parameters,level)
    val param = (random_int (1,a),b,c,d)
    val p = random_prog param
    val ol = ol_of_statel (map (exec_prog p) statel_org)
  in
    (ol,(p,length p))
  end

fun list_snd_imin l = case l of 
    [] => raise ERR "list_snd_imin" ""
  | [(p,n)] => (p,n)
  | (p,n) :: m => 
    let val (p',n') = list_snd_imin m in 
      if n < n' then (p,n) else (p',n')
    end

fun random_prefix p = first_n (random_int (0,length p - 1)) p

fun gen_olsizel level =
  let 
    val olsizel1 = List.tabulate (100000, fn _ => rand_olsize level) 
    val olsizel2 = map_snd list_snd_imin (dlist (dregroup compare_ol olsizel1))
  in
    olsizel2
  end

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

fun mk_targetl level ntarget =
  let 
    val l1 = gen_olsizel level 
    val l2 = first_n ntarget (shuffle l1)
    val l3 = map_snd (fn (p,n) => (random_prefix p,n)) l2
  in
    map mk_startsit l3
  end

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val gamespec : (board,move) mlReinforce.gamespec =
  {
  movel = movel_ext,
  move_compare = move_compare,
  string_of_move = string_of_move,
  filter_sit = filter_sit,
  status_of = status_of,
  apply_move = apply_move_ext,
  operl = program_operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  max_bigsteps = max_bigsteps
  }

val extspec = mk_extspec "mleProgram.extspec" gamespec

(* -------------------------------------------------------------------------
   Reinforcement learning
   ------------------------------------------------------------------------- *)

(*
load "mleProgram"; open mleProgram;
load "mlReinforce"; open mlReinforce;
load "smlParallel"; open smlParallel;
load "aiLib"; open aiLib;

level_parameters := 
  let fun f (n1,n2) = List.tabulate (n2 - n1 + 1, fn x => x + n1) in
    map (quadruple_of_list o rev) (cartesian_productl 
      (map f (rev [(4,32),(4,4),(4,4),(1,1)])))
  end;

psMCTS.alpha_glob := 0.3;
psMCTS.exploration_coeff := 2.0;
logfile_glob := "program_run53";
parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^
(!logfile_glob);
ncore_mcts_glob := 8;
ncore_train_glob := 8;
ntarget_compete := 400;
ntarget_explore := 400;
exwindow_glob := 10000;
uniqex_flag := false;
dim_glob := 8;
lr_glob := 0.02;
batchsize_glob := 16;
decay_glob := 0.99;
level_glob := 0;
nsim_glob := 1600;
nepoch_glob := 20;
ngen_glob := 100;
temp_flag := true;
level_threshold := 0.8;

start_rl_loop (gamespec,extspec);
*)

(* -------------------------------------------------------------------------
   Small tests
   ------------------------------------------------------------------------- *)

(*
fun mk_ol binop = 
  let fun f x = binop (dfind 1 x, dfind 2 x) in map f statel_org end
*)

end (* struct *)
