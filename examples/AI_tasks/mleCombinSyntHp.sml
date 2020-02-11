(* ========================================================================= *)
(* FILE          : mleCombinSyntHp.sml                                       *)
(* DESCRIPTION   : Specification of term synthesis on combinator datatype    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleCombinSyntHp :> mleCombinSyntHp =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mleCombinLib mleCombinLibHp

val ERR = mk_HOL_ERR "mleCombinSyntHp"
val version = 4
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (combin * pose list * bool) * combin * int
fun string_of_board ((c1,pos,b),c2,n)= 
  combin_to_string c1 ^ " " ^ pos_to_string pos ^ 
  combin_to_string c2 ^ " " ^ its n

fun board_compare ((a,b,c),(d,e,f)) =
  (cpl_compare 
   (triple_compare combin_compare pos_compare bool_compare) combin_compare) 
  ((a,b),(d,e))

fun fullboard_compare ((a,b,c),(d,e,f)) =
  (triple_compare 
     Int.compare
    (triple_compare combin_compare pos_compare bool_compare) 
     combin_compare
  )   
  ((c,a,b),(f,d,e))


fun status_of ((c1,_,b),c2,n) =
  let val nfo = if b orelse c1 = V1 
                then NONE 
                else hp_norm 100 (A(A(A(c1,V1),V2),V3)) 
  in
    if isSome nfo andalso valOf nfo = c2 then Win
    else if n <= 0 then Lose else Undecided
  end

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = AS | AK | NextPos

val movel = [AS,AK,NextPos]

fun string_of_move move = case move of
    AS => "AS"
  | AK => "AK"
  | NextPos => "NextPos"

fun move_compare (m1,m2) = 
  String.compare (string_of_move m1, string_of_move m2)

exception Redex

fun add_apply sk n (c,pos) = case (c,pos) of
    (A(c1,c2), Left :: m) => A (add_apply sk (n+1) (c1,m), c2)
  | (A(c1,c2), Right :: m) => A (c1, add_apply sk 0 (c2,m))
  | (S, []) => if n >= 2 then raise Redex else A(S,sk)
  | (K, []) => if n >= 1 then raise Redex else A(K,sk)
  | _ => raise ERR "add_apply" "position_mismatch"

fun apply_move move ((c1,pos,_),c2,n) = 
  if c1 = V1 then 
    (
    case move of
      AS => ((S,[],false), c2, n-1)
    | AK => ((K,[],false), c2, n-1)
    | NextPos => raise Redex
    )
  else 
    (
    case move of
      AS => ((add_apply S 0 (c1,pos), pos @ [Left], false), c2, n-1)
    | AK => ((add_apply K 0 (c1,pos), pos @ [Left], false), c2, n-1)
    | NextPos => (((c1,next_pos pos, true), c2, n-1) 
                  handle HOL_ERR _ => raise Redex)
    )

fun available_movel board =
  filter (fn x => (ignore (apply_move x board); true) 
          handle Redex => false) movel

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  apply_move = apply_move,
  available_movel = available_movel,  
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movel
  }

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let 
    val (l1,l2,l3) = split_triple boardl 
    val (l1a,l1b,l1c) = split_triple l1
  in
    export_terml (file ^ "_in") (map hp_to_cterm l1a);
    writel (file ^ "_pos") (map pos_to_string l1b);
    writel (file ^ "_bool") (map bts l1c);
    export_terml (file ^ "_out") (map hp_to_cterm l2); 
    writel (file ^ "_timer") (map its l3)
  end

fun read_boardl file =
  let
    val l1a = map cterm_to_hp (import_terml (file ^ "_in"))
    val l1b = map string_to_pos (readl_empty (file ^ "_pos"))
    val l1c = map string_to_bool (readl_empty (file ^ "_bool"))
    val l2 = map cterm_to_hp (import_terml (file ^ "_out"))
    val l3 = map string_to_int (readl (file ^ "_timer"))
  in
    combine_triple (combine_triple (l1a,l1b,l1c),l2,l3)
  end

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/combin_target"
fun import_targetl name = 
  let 
    val f = #read_boardl (#gameio (mleCombinSynt.rlobj))
    val boardl = f (targetdir ^ "/" ^ name)
    fun g (a,b,c) = ((V1,[],false), cterm_to_hp b, c)
  in
    map g boardl
  end

fun mk_targetd l1 =
  let 
    val l2 = number_snd 0 l1
    val l3 = map (fn (x,i) => (x,(i,[]))) l2
  in
    dnew board_compare l3
  end

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/combin_target"

fun create_targetl l =
  let 
    val (train,test) = part_pct (10.0/11.0) (shuffle l)
    val _ = export_data (train,test)
    fun f (headnf,combin) = ((V1,[],false), headnf , 2 * combin_size combin)
  in
    (dict_sort fullboard_compare (map f train),
     dict_sort fullboard_compare (map f test))
  end

fun export_targetl name targetl = 
  let val _ = mkDir_err targetdir in 
    write_boardl (targetdir ^ "/" ^ name) targetl
  end

fun import_targetl name = read_boardl (targetdir ^ "/" ^ name)
 
fun mk_targetd l1 =
  let 
    val l2 = number_snd 0 l1
    val l3 = map (fn (x,i) => (x,(i,[]))) l2
  in
    dnew board_compare l3
  end

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val head_eval = mk_var ("head_eval", ``:bool -> 'a``)
val head_poli = mk_var ("head_poli", ``:bool -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)

fun convert_pos pos = 
  let fun f x = case x of Left => 0 | Right => 1 in
    map f pos
  end

fun tob1 ((c1,pos,_),c2,_) = 
  let 
    val (tm1,tm2) = (hp_to_cterm c1, hp_to_cterm c2)
    val tm = mk_eq (tag_pos (tm1,convert_pos pos), tm2)
  in
    [tag_heval tm, tag_hpoli tm]
  end

fun tob2 embedv ((c1,pos,_),_,_) = 
  let 
    val (tm1,tm2) = (hp_to_cterm c1, embedv)
    val tm = mk_eq (tag_pos (tm1,convert_pos pos), tm2)
  in
    [tag_heval tm, tag_hpoli tm]
  end

fun pretob boardtnno = case boardtnno of
    NONE => tob1
  | SOME ((_,headnf,_),tnn) => 
    tob2 (precomp_embed tnn (hp_to_cterm headnf))

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10}]

val dim = 16
fun dim_head_poli n = [dim,n]
val tnnparam = map_assoc (dim_std (1,dim)) 
  [``$= : 'a -> 'a -> bool``,cT,v1,v2,v3,cA,cS,cK] @ 
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]

val dplayer = {pretob = pretob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleCombinSyntHp-" ^ its version, exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer}

val extsearch = mk_extsearch "mleCombinSyntHp.extsearch" rlobj

(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleCombinLibHp"; open mleCombinLibHp;
load "mleCombinSyntHp"; open mleCombinSyntHp;

val (dfull,ntry) = gen_headnf 2200 (dempty combin_compare);
val (train,test) = create_targetl (dlist dfull); length train; length test;
val _ = (export_targetl "train" train; export_targetl "test" test);

val targetl = import_targetl "train";
val r = rl_start (rlobj,extsearch) (mk_targetd targetl);

val targetd = retrieve_targetd rlobj 18;
val _ = rl_restart 18 (rlobj,extsearch) targetd;
*)

(* -------------------------------------------------------------------------
   Big steps test
   ------------------------------------------------------------------------- *)

(*
load "mleCombinLibHp"; open mleCombinLibHp;
load "mleCombinSyntHp"; open mleCombinSyntHp;
load "mlReinforce"; open mlReinforce;
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "psBigSteps" ; open psBigSteps;

val mctsparam =
  {
  nsim = 3200,
  stopatwin_flag = false,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = false,
  avoidlose = false
  };

val bsobj : (board,move) bsobj =
  {
  verbose = true,
  temp_flag = false,
  player = psMCTS.random_player (#game rlobj),
  game = (#game rlobj),
  mctsparam = mctsparam
  };

val targetl = import_targetl "sy9";
val target = List.nth (targetl,150);
val _ = run_bigsteps bsobj target;
*)


end (* struct *)
