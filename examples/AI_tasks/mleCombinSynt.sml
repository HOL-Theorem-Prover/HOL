(* ========================================================================= *)
(* FILE          : mleCombinSynt.sml                                         *)
(* DESCRIPTION   : Specification of term synthesis on combinator datatype    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleCombinSynt :> mleCombinSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mleCombinLib

val ERR = mk_HOL_ERR "mleCombinSynt"
val version = 5
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Board: synthesized combinator * head normal form * timer
   V1 used as a meta variable in the synthesized combinator.
   ------------------------------------------------------------------------- *)

type board = combin * combin * int  

fun string_of_board (c1,c2,n)= 
  combin_to_string c1 ^ "\n" ^ combin_to_string c2 ^ "\n" ^ its n

fun board_compare ((a,b,c),(d,e,f)) =
  (cpl_compare combin_compare combin_compare) ((a,b),(d,e))

fun fullboard_compare ((a,b,c),(d,e,f)) =
  (triple_compare Int.compare combin_compare combin_compare) ((c,a,b),(f,d,e))

fun ignore_metavar c = case c of
    A(c1,V1) => ignore_metavar c1
  | A(c1,c2) => A(c1, ignore_metavar c2) 
  | S => S
  | K => K
  | _ => raise ERR "ignore_metavar" ""

fun no_metavar c = case c of    
    A(c1,c2) => no_metavar c1 andalso no_metavar c2
  | V1 => false
  | _ => true

fun status_of (c1,c2,n) =
  if c1 = V1 then Undecided else
  let
    val c1' = ignore_metavar c1
    val nfo = combin_norm 100 (A(A(A(c1',V1),V2),V3)) 
  in
    if isSome nfo andalso valOf nfo = c2 then Win
    else if n <= 0 then Lose else Undecided
  end

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = S0 | S1 | S2 | K0 | K1

val movel = [S0,S1,S2,K0,K1]

fun string_of_move move = case move of
    S0 => "S0"
  | S1 => "S1"
  | S2 => "S2"
  | K0 => "K0"
  | K1 => "K1"

fun move_compare (m1,m2) = 
  String.compare (string_of_move m1, string_of_move m2)

fun res_of_move move = case move of
    S0 => S
  | S1 => A(S,V1)
  | S2 => A(A(S,V1),V1)
  | K0 => K
  | K1 => A(K,V1)

fun replace_metavar move c = case c of
    A(c1,c2) => 
    let val c1o = replace_metavar move c1 in
      case c1o of
        NONE => 
        let val c2o = replace_metavar move c2 in
          case c2o of NONE => NONE | SOME c2new => SOME (A(c1,c2new))
        end
      | SOME c1new => SOME (A(c1new,c2))
    end
  | V1 => SOME (res_of_move move)
  | _ => NONE

exception Break;  

fun apply_move move (c1,c2,n) =
  (let val c1new = valOf (replace_metavar move c1) in
     if no_metavar c1new then raise Break else c1new 
   end, 
   c2, n-1)  

fun available_movel board = 
  ((ignore ((apply_move S0) board); movel) handle Break => [S1,S2,K1])

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  available_movel = available_movel,
  apply_move = apply_move,
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
  in
    export_terml (file ^ "_witness") (map combin_to_cterm l1);
    export_terml (file ^ "_headnf") (map combin_to_cterm l2); 
    writel (file ^ "_timer") (map its l3)
  end

fun read_boardl file =
  let
    val l1 = map cterm_to_combin (import_terml (file ^ "_witness"))
    val l2 = map cterm_to_combin (import_terml (file ^ "_headnf"))
    val l3 = map string_to_int (readl (file ^ "_timer"))
  in
    combine_triple (l1,l2,l3)
  end

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/combin_target"

fun create_targetl l =
  let 
    val (train,test) = part_pct (10.0/11.0) (shuffle l)
    val _ = export_data (train,test)
    fun f (headnf,combin) = (V1, headnf, 2 * combin_size combin)
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

val cS0 = mk_var ("s0",``:'a``)
val cS1 = mk_var ("s1",``:'a -> 'a ``)
val cS2 = mk_var ("s2",``:'a -> 'a -> 'a``)
val cK0 = mk_var ("k0",``:'a``)
val cK1 = mk_var ("k1",``:'a -> 'a ``)
val v1a0 = mk_var ("v1a0",``:'a``)
val v1a1 = mk_var ("v1a1",``:'a -> 'a``)
val v1a2 = mk_var ("v1a2",``:'a -> 'a -> 'a``)
val v1a3 = mk_var ("v1a3",``:'a -> 'a -> 'a -> 'a``)
val v1a4 = mk_var ("v1a4",``:'a -> 'a -> 'a -> 'a -> 'a``)
val v2a0 = mk_var ("v2a0",``:'a``)
val v2a1 = mk_var ("v2a1",``:'a -> 'a``)
val v2a2 = mk_var ("v2a2",``:'a -> 'a -> 'a``)
val v2a3 = mk_var ("v2a3",``:'a -> 'a -> 'a -> 'a``)
val v2a4 = mk_var ("v2a4",``:'a -> 'a -> 'a -> 'a -> 'a``)
val v3a0 = mk_var ("v3a0",``:'a``)
val v3a1 = mk_var ("v3a1",``:'a -> 'a``)
val v3a2 = mk_var ("v3a2",``:'a -> 'a -> 'a``)
val v3a3 = mk_var ("v3a3",``:'a -> 'a -> 'a -> 'a``)
val v3a4 = mk_var ("v3a4",``:'a -> 'a -> 'a -> 'a -> 'a``)
val metavar = mk_var ("metavar",``:'a``)
val skvarl = 
  [cS0,cS1,cS2,cK0,cK1,
   v1a0,v1a1,v1a2,v1a3,v1a4, 
   v2a0,v2a1,v2a2,v2a3,v2a4,
   v3a0,v3a1,v3a2,v3a3,v3a4,metavar]

fun witness_to_nntm combin = case combin of
    A(A(S,x),y) => list_mk_comb (cS2, map witness_to_nntm [x,y])
  | A(S,x) => mk_comb (cS1, witness_to_nntm x)
  | S => cS0
  | A(K,x) => mk_comb (cK1, witness_to_nntm x)
  | K => cK0
  | V1 => metavar
  | _ => raise ERR "witness_to_nntm" (combin_to_string combin)

fun headnf_to_nntm combin = case combin of
    A(A(A(A(V1,x),y),z),w) => 
    list_mk_comb (v1a4, map headnf_to_nntm [x,y,z,w])
  | A(A(A(V1,x),y),z) =>
    list_mk_comb (v1a3, map headnf_to_nntm [x,y,z])
  | A(A(V1,x),y) => 
    list_mk_comb (v1a2, map headnf_to_nntm [x,y])
  | A(V1,x) => mk_comb (v1a1, headnf_to_nntm x)
  | V1 => v1a0
  | A(A(A(A(V2,x),y),z),w) => 
    list_mk_comb (v2a4, map headnf_to_nntm [x,y,z,w])
  | A(A(A(V2,x),y),z) =>
    list_mk_comb (v2a3, map headnf_to_nntm [x,y,z])
  | A(A(V2,x),y) => 
    list_mk_comb (v2a2, map headnf_to_nntm [x,y])
  | A(V2,x) => mk_comb (v2a1, headnf_to_nntm x)
  | V2 => v2a0
  | A(A(A(A(V3,x),y),z),w) => 
    list_mk_comb (v3a4, map headnf_to_nntm [x,y,z,w])
  | A(A(A(V3,x),y),z) =>
    list_mk_comb (v3a3, map headnf_to_nntm [x,y,z])
  | A(A(V3,x),y) => 
    list_mk_comb (v3a2, map headnf_to_nntm [x,y])
  | A(V3,x) => mk_comb (v3a1, headnf_to_nntm x)
  | V3 => v3a0
  | _ => raise ERR "headnf_to_nntm" ""

fun convert_pos pos = 
  let fun f x = case x of Left => 0 | Right => 1 in
    map f pos
  end

fun tob1 (c1,c2,_) = 
  let 
    val (tm1,tm2) = (witness_to_nntm c1, headnf_to_nntm c2)
    val tm = mk_eq (tm1,tm2)
  in
    [tag_heval tm, tag_hpoli tm]
  end

fun tob2 embedv (c1,_,_) = 
  let 
    val (tm1,tm2) = (witness_to_nntm c1, embedv)
    val tm = mk_eq (tm1,tm2)
  in
    [tag_heval tm, tag_hpoli tm]
  end

fun pretob boardtnno = case boardtnno of
    NONE => tob1
  | SOME ((_,headnf,_),tnn) => 
    tob2 (precomp_embed tnn (headnf_to_nntm headnf))

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10}]

val dim = 16
fun dim_head_poli n = [dim,n]
val tnnparam = map_assoc (dim_std (1,dim)) 
  ([``$= : 'a -> 'a -> bool``] @ skvarl) @ 
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]

val dplayer = {pretob = pretob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleCombinSynt-" ^ its version, exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer}

val extsearch = mk_extsearch "mleCombinSynt.extsearch" rlobj

(* -------------------------------------------------------------------------
   Final test
   ------------------------------------------------------------------------- *)

val ft_extsearch_uniform = 
  ft_mk_extsearch "mleCombinSynt.ft_extsearch_uniform" rlobj
    (uniform_player game) 

val fttnn_extsearch =
  fttnn_mk_extsearch "mleCombinSynt.fttnn_extsearch" rlobj

val fttnnbs_extsearch =
  fttnnbs_mk_extsearch "mleCombinSynt.fttnnbs_extsearch" rlobj

(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleCombinLib"; open mleCombinLib;
load "mleCombinSynt"; open mleCombinSynt;

val (dfull,ntry) = gen_headnf 2200 (dempty combin_compare);
val (train,test) = create_targetl (dlist dfull); length train; length test;
val _ = (export_targetl "train" train; export_targetl "test" test);

val targetl = import_targetl "train";
val r = rl_start (rlobj,extsearch) (mk_targetd targetl);

val targetd = retrieve_targetd rlobj 83;
val _ = rl_restart 83 (rlobj,extsearch) targetd;
*)

(* -------------------------------------------------------------------------
   MCTS test for manual inspection
   ------------------------------------------------------------------------- *)

(*
load "mleCombinLib"; open mleCombinLib;
load "mleCombinSynt"; open mleCombinSynt;
load "mlReinforce"; open mlReinforce;
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

val mctsparam =
  {
  timer = SOME 5.0,
  nsim = NONE,
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = false,
  avoidlose = false
  };

val game = #game rlobj;
val mctsobj = {game = game, mctsparam = mctsparam, 
  player =  psMCTS.random_player (#game rlobj)};

val headnf = A(V2,(list_mk_A[V1,V2,V3]));
val target = (V1,headnf,100);
val tree = psMCTS.starttree_of mctsobj target;
val (newtree,_) = mcts mctsobj tree;
val nodel = trace_win (#status_of game) newtree [];
*)

(* -------------------------------------------------------------------------
   Final testing
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "smlParallel"; open smlParallel;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleCombinSynt"; open mleCombinSynt;

val dir1 = HOLDIR ^ "/examples/AI_tasks/combin_results_nolimit";
val _ = mkDir_err dir1;
fun store_result dir (a,i) = 
  #write_result ft_extsearch_uniform (dir ^ "/" ^ its i) a;

(*** Test ***)
val dataset = "test";
val pretargetl = import_targetl dataset; 
val targetl = map (fn (a,b,_) => (a,b,1000000)) pretargetl; 
length targetl; 
(* uniform *)
val (l1',t) = 
  add_time (parmap_queue_extern 20 ft_extsearch_uniform ()) targetl;
val winb = filter I (map #1 l1'); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_uniform";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l1');
(* tnn *)
val tnn = mlReinforce.retrieve_tnn rlobj 318;
val (l2',t) = add_time (parmap_queue_extern 20 fttnn_extsearch tnn) targetl;
val winb = filter I (map #1 l2'); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_tnn";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l2');

(*** Train ***)
val dataset = "train";
val pretargetl = import_targetl dataset; 
val targetl = map (fn (a,b,_) => (a,b,1000000)) pretargetl; 
length targetl; 
(* uniform *)
val (l1,t) = add_time (parmap_queue_extern 20 ft_extsearch_uniform ()) targetl;
val winb = filter I (map #1 l1); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_uniform";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l1);
(* tnn *)
val tnn = mlReinforce.retrieve_tnn rlobj 318;
val (l2,t) = add_time (parmap_queue_extern 20 fttnn_extsearch tnn) targetl;
val winb = filter I (map #1 l2); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_tnn";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l2);
*)

(* -------------------------------------------------------------------------
   Final testing statistics
   ------------------------------------------------------------------------- *)

(*
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val (bstatus,nstep,boardo) = g 0;
*)

end (* struct *)
