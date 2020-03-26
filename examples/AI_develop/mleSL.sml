(* ========================================================================= *)
(* FILE          : mleSL.sml                                                 *)
(* DESCRIPTION   : Supervised learning as a reinforcement learning game      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleSL :> mleSL =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork


val selfdir = HOLDIR ^ "/examples/AI_develop"

load "aiLib"; open aiLib;
val ERR = mk_HOL_ERR "mleSL";

datatype prop = 
  False | True | 
  Neg of prop |
  Imp of prop * prop | 
  Or of prop * prop | 
  And of prop * prop |
  Var of int;

fun eval_ground ba prop = case prop of
    False => false 
  | True => true
  | Neg p => not (eval_ground ba p)
  | Imp (p1,p2) => not (eval_ground ba p1) orelse eval_ground ba p2
  | Or (p1,p2) => eval_ground ba p1 orelse eval_ground ba p2 
  | And (p1,p2) => eval_ground ba p1 andalso eval_ground ba p2
  | Var n => Vector.sub (ba,n)
;

fun prop_to_term prop = case prop of
    False => F
  | True => T
  | Neg p => mk_neg (prop_to_term p)
  | Imp (p1,p2) => mk_imp (prop_to_term p1, prop_to_term p2)
  | Or (p1,p2) => mk_disj (prop_to_term p1, prop_to_term p2)
  | And (p1,p2) => mk_conj (prop_to_term p1, prop_to_term p2)
  | Var n => mk_var ("v" ^ its n,bool) 
;

fun eval_forall prop =
  let
    val vl = map Vector.fromList
      (cartesian_productl (List.tabulate (5,fn _ => [true,false])))
  in
    all (fn x => eval_ground x prop) vl
  end;






(* -------------------------------------------------------------------------
   2-player game
   ------------------------------------------------------------------------- *)

load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val ERR = mk_HOL_ERR "mleSL";
val start = mk_var ("start",alpha);
val s0 = mk_var ("s0",``:'a -> 'a``);
val s1 = mk_var ("s1",``:'a -> 'a``);
val head_ = mk_var ("head_",``:'a -> 'a -> 'a -> 'a``);

val tnnparam = 
  [
  (start, [0,12]),
  (s0, [12,12,12]),
  (s1, [12,12,12]),
  (head_,[12*2,12,2])
  ];

fun play_tnn tnn tm =
  let 
    val (_,r2) = singleton_of_list (infer_tnn tnn [tm])
    val (r2a,r2b) = pair_of_list r2
  in
    r2a > r2b
  end;

fun play_simul (ex1,ex2) (tnn1,tnn2) (tm1,tm2) =
  let 
    val t1 = list_mk_comb (head_,[tm1,tm2])
    val r1 = play_tnn tnn1 t1
    val t2 = list_mk_comb (head_,[start,tm2])
    val r2 = play_tnn tnn2 t2
    val newtm1 = if r1 then mk_comb (s1,tm1) else mk_comb (s0,tm1)
    val newtm2 = if r2 then mk_comb (s1,tm2) else mk_comb (s0,tm2)
  in
    ex1 := (t1, if r2 then [0.0,1.0] else [1.0,0.0]) :: !ex1;
    ex2 := (t2, if r1 then [1.0,0.0] else [0.0,1.0]) :: !ex2;
    (newtm1,newtm2)
  end

fun score (game1,game2) = 
  if is_var game1 then 0 else
  let 
    val (oper1,cont1) = dest_comb game1
    val (oper2,cont2) = dest_comb game2
  in
    (if term_eq oper1 oper2 then 1 else 0) + score (cont1,cont2)
  end

val (ex1,ex2) : (term * real list) list ref * (term * real list) list ref =
 (ref [],ref []);

val schedule1 =
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 2, nepoch = 25}] @
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 4, nepoch = 25}]

val schedule2 =
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 2, nepoch = 10}] @
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 4, nepoch = 10}]

fun loop n =
  let
    val tnn1 = if null (!ex1) then random_tnn tnnparam else
    train_tnn schedule1 (random_tnn tnnparam) (map single (!ex1),[]);
    val tnn2 = if null (!ex2) then random_tnn tnnparam else
    train_tnn schedule2 (random_tnn tnnparam) (map single (!ex2),[]);
    val (game1,game2) = 
       funpow 32 (play_simul (ex1,ex2) (tnn1,tnn2)) (start,start);
  in
    print_endline (its (score (game1,game2)));
    app (print_endline o tts) [game1,game2];
    if (n-1) <= 0 then () else loop (n-1)
  end;

loop 100;

(* 
Synthesizing 
intermediate lemmas for helping to decide propositional formulas 
*)


(* -------------------------------------------------------------------------
   A list of terms
   ------------------------------------------------------------------------- *)

val thml1 = List.concat (map DB.thms ["arithmetic"]);
val thml2 = map snd thml1;

fun mk_lam (v,bod) =
  let 
    val ty1 = type_of v
    val ty2 = type_of bod
    val ty3 = mk_type ("fun",[ty1,ty2])
    val ty4 = mk_type ("fun",[ty1, mk_type ("fun",[ty2,ty3])])
  in
    mk_var ("lam",ty4)
  end

fun name_of_cv cv = 
  if is_var cv then fst (dest_var cv)
  else if is_const cv then fst (dest_const cv)
  else raise ERR "name_of_cv" ""

fun convert_lam tm = case dest_term tm of
    COMB (tm1,tm2) => mk_comb (convert_lam tm1, convert_lam tm2)
  | LAMB (v,bod) => list_mk_comb (mk_lam (v,bod),[v,convert_lam bod])
  | _ => tm

fun convert_arity tm =   
  let 
    val (oper,argl) = strip_comb tm 
    val name = name_of_cv oper ^ "_arity_" ^ its (length argl)
    val v = mk_var (name, type_of oper)
  in
    list_mk_comb (v, map convert_arity argl)
  end

val tml1 = map (list_mk_imp o dest_thm) thml2;
val tml2 = map (convert_arity o convert_lam) tml1;

(* -------------------------------------------------------------------------
   Substitution
   ------------------------------------------------------------------------- *)

(* todo: make the final reward function *)

val vl' = List.concat (map (find_terms is_var) tml2);
val vld = dlist (count_dict (dempty Term.compare) vl');
val vld2 = dict_sort compare_imax vld;
val vld3 = filter (fn x => snd x >= 4) vld2;

val vl = mk_term_set (List.concat (map (find_terms is_var) tml2));


fun vx_of ty = mk_var ("X",ty);
fun is_X tm = is_var tm  andalso fst (dest_var tm) = "X"

fun subst_of_var v = 
  let 
    val name = fst (dest_var v) 
    val arity = (string_to_int o snd o split_string "_arity_") name
    val (tyl,im) = strip_type_n arity (type_of v)
  in
    [{redex = vx_of im, residue = list_mk_comb (v, map vx_of tyl)}]
  end;

val substl = map subst_of_var vl;

(* -------------------------------------------------------------------------
   Prefix
   ------------------------------------------------------------------------- *)

fun before_X f l = case l of
    [] => raise ERR "before_X" ""
  | [a] => 
    if is_X a then raise ERR "before_X" "" else [f a]
  | a :: b :: m => 
    if is_X b then f a :: b :: m else a :: before_X f (b :: m)

fun prefix_of_aux r tm =
  let val (oper,argl) = strip_comb tm in
    if null argl orelse all is_X argl 
    then (r := oper; vx_of (type_of tm)) 
    else list_mk_comb (oper, before_X (prefix_of_aux r) argl)
  end

fun prefix_of tm = 
  let 
    val r = ref F 
    val prefix = prefix_of_aux r tm
  in 
    (!r,prefix)
  end

fun all_prefix tm =
  if is_X tm then [] else
  let val (oper,prefix) = prefix_of tm in
    (oper,prefix) :: all_prefix prefix
  end

(* -------------------------------------------------------------------------
   Policy examples
   ------------------------------------------------------------------------- *)

fun head_of n tm = 
  mk_comb (mk_var ("head_" ^ its n, 
           mk_type ("fun",[type_of tm,alpha])), tm); 

fun ex_of (oper,prefix) = 
  let 
    val res = #residue (hd (subst_of_var oper))
    val curx = find_term is_X prefix
    val cursubl = filter (fn x => term_eq (#redex (hd x)) curx) substl
    fun f sub = if term_eq (#residue (hd sub)) res then 1.0 else 0.0
  in
    (head_of (length cursubl) prefix, map f cursubl)
  end

fun ex_of_tm tm = map ex_of (rev (all_prefix tm));
val exl = List.concat (map ex_of_tm tml2);
val exl2 = map single exl;

fun is_head v = String.isPrefix "head_" (fst (dest_var v));
val operl = mk_term_set (List.concat (map free_vars (map fst exl @ tml2)));
val (operlh, operln) = partition is_head operl;

fun dim_opern dim oper =
  if is_X oper then (oper,[0,dim]) else
  let     
    val name = fst (dest_var oper) 
    val arity = (string_to_int o snd o split_string "_arity_") name
  in
    (oper,[dim * arity,dim])
  end

fun dim_operh dim oper =
  let     
    val name = fst (dest_var oper) 
    val dimout = (string_to_int o snd o split_string "_") name
  in
    (oper,[dim,dimout])
  end

val tnnparam = map (dim_opern 12) operln @ map (dim_operh 12) operlh;

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

val randtnn = random_tnn tnnparam;
val schedule =
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 2, nepoch = 10}] @
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 4, nepoch = 10}]  @
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 8, nepoch = 10}];

val tnn = train_tnn schedule randtnn (first_n 10000 (shuffle exl2),[]);
val _ = write_tnn (HOLDIR ^ "/examples/AI_develop/tnn_arith") tnn;

fun next_guess tnn b ptm = 
  let 
    val curx = find_term is_X ptm
    val cursubl = filter (fn x => term_eq (#redex (hd x)) curx) substl
    val nntm = head_of (length cursubl) ptm
    val rl = snd (singleton_of_list (infer_tnn tnn [nntm]))
    val sub = (if b then best_in_distrib else select_in_distrib) 
      (combine (cursubl,rl))
  in
    subst_occs [[1]] sub ptm
  end

fun best_guess tnn b ptm =
  if can (find_term is_X) ptm
  then best_guess tnn b (next_guess tnn b ptm)
  else ptm

fun pts tm = 
  let val (oper,argl) = strip_comb tm in
    if null argl 
    then (fst o (split_string "_arity_") o fst o dest_var) oper
    else "(" ^ 
         (fst o (split_string "_arity_") o fst o dest_var) oper ^ " " ^
         String.concatWith " " (map pts argl) ^ ")"
  end;

pts (best_guess tnn true (vx_of bool));
pts (best_guess tnn false (vx_of bool));

val tm = best_guess tnn false (vx_of bool);
val equalnum = mk_var ("=_arity_2", ``: num -> num -> bool``);
val equaltm = list_mk_comb (equalnum, [vx_of ``:num``,vx_of ``:num``]);
pts (best_guess tnn false equaltm);

val equalnum = mk_var ("==>_arity_2", ``: bool -> bool -> bool``);
val equaltm = list_mk_comb (equalnum, [vx_of bool,vx_of bool]);
pts (best_guess tnn false equaltm);


end (* struct *)
