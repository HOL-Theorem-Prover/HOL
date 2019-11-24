(* ========================================================================= *)
(* FILE          : mleSetLib.sml                                             *)
(* DESCRIPTION   : Library for synthesis of formulas in Set Theory           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSetLib :> mleSetLib =
struct

open HolKernel Abbrev boolLib aiLib mleLib
val ERR = mk_HOL_ERR "mleSetLib"

fun ilts n = String.concat (map its n)

(* -------------------------------------------------------------------------
   Operators
   ------------------------------------------------------------------------- *)

val tEmpty = mk_var ("tEmpty",alpha)
val tPower = mk_var ("tPower",``:'a -> 'a``)
val tSing  = mk_var ("tSing",``:'a -> 'a``)
val tbinunion = mk_var ("tbinunion", ``:'a -> 'a -> 'a``)
val constrl = [tEmpty,tPower,tSing,tbinunion];
fun is_constr t = tmem t constrl;

val binpred = ``:'a -> 'a -> bool``
val pEQ = mk_var ("pEQ", binpred)
val pIn = mk_var ("pIn", binpred)
val pSubq = mk_var ("pSubq", binpred)
val predl = [pEQ,pIn,pSubq]

(* logical operators *)
val oNOT = mk_var ("oNOT", ``:bool -> bool``)
val oIMP = mk_var ("oIMP", ``:bool -> bool -> bool``)
val oAND = mk_var ("oAND", ``:bool -> bool -> bool``)
val logicopl = [oNOT,oIMP,oAND]
fun is_logicop t = tmem t logicopl

(* quantifies *)
val quant_type = ``:'a -> 'a -> bool -> bool``
val qFORALL_IN = mk_var ("qFORALL_IN",quant_type)
val qFORALL_SUBQ = mk_var ("qFORALL_SUBQ",quant_type)
val qEXISTS_IN = mk_var ("qEXISTS_IN",quant_type)
val qEXISTS_SUBQ = mk_var ("qEXISTS_SUBQ",quant_type)
val quantl = [qFORALL_IN,qFORALL_SUBQ,qEXISTS_IN,qEXISTS_SUBQ]
fun is_quant t = tmem t quantl;

(* variables *)
val max_quants = 4;
val yvarl = List.tabulate (max_quants, fn i => mk_var ("vY" ^ its i,alpha));
val xvar = mk_var ("vX",alpha);
val xvarl = [xvar];
val cont_term = mk_var ("cont_term",``:'a list -> 'a``);
val cont_form = mk_var ("cont_form", ``:'a list -> bool``);
val contl = [cont_term,cont_form]
fun is_cont t = tmem t contl;
fun is_xyvar t = tmem t (xvarl @ yvarl);

val operl_plain = constrl @ predl @ logicopl @ quantl @ xvarl @ yvarl

(* remove NOT move and introduce extra moves instead *)
val pNOTEQ = mk_var ("pNOTEQ", binpred)
val pNOTIn = mk_var ("pNOTIn", binpred)
val pNOTSubq = mk_var ("pNOTSubq", binpred)
val notpred_adict = dnew Term.compare
  [(pNOTEQ,pEQ),(pNOTIn,pIn),(pNOTSubq,pSubq)]
val notpredl = [pNOTEQ,pNOTIn,pNOTSubq]
fun is_predmove t = tmem t (predl @ notpredl);

val movel = constrl @ predl @ notpredl @ [oIMP,oAND] @ quantl @ xvarl @ yvarl

(* -------------------------------------------------------------------------
   Writing terms
   ------------------------------------------------------------------------- *)

fun setname_to_lisp s =
  let
    fun f c = if c = #"_" then "-" else Char.toString c
    val s1 = tl_string (String.translate f s)
    fun test x = Char.isUpper x orelse Char.isDigit x orelse x = #"-"
  in
    if all test (explode s1) then s1 else quote s1
  end

fun setterm_to_lisp t =
  if is_var t then setname_to_lisp (fst (dest_var t)) else
  let val (a,b) = dest_comb t in
    ("(" ^ setterm_to_lisp a ^ " . " ^ setterm_to_lisp b ^ ")")
  end

(*
load "mleSetLib"; open mleSetLib;
load "aiLib"; open aiLib;
val formula = (funpow 20 random_step) start_form;
fun contains_cont t = can (find_term is_cont) t
fun gen_nform n =
  if n <= 0 then [] else
  let val form = (funpow 20 random_step) start_form in
    if contains_cont form
    then gen_nform n
    else form :: gen_nform (n-1)
  end
val forml10 = gen_nform 10;
writel "exholformat" (map setterm_to_lisp forml10);
*)

(* -------------------------------------------------------------------------
   Reading terms
   ------------------------------------------------------------------------- *)

val setsyntdata_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"
val train_file = setsyntdata_dir ^ "/train_sexpr"

fun read_info sexprl = case sexprl of
    [Lterm [a,b,c,d]] => (a,b,c,d)
  | x => raise ERR "read_info" (PolyML.makestring sexprl)

fun list_mk_AP l =
  list_mk_comb (hd l,tl l) handle Empty => raise ERR "list_mk_AP" ""

val stringterm_dict =
  dnew String.compare (map swap
  (map_assoc (setname_to_lisp o fst o dest_var) operl_plain))

fun parse_term sexpr = case sexpr of
    Lterm (Lstring "AP" :: m) => list_mk_AP (map parse_term m)
  | Lterm l => list_mk_AP (map parse_term l)
  | Lstring s => dfind s stringterm_dict
    handle NotFound => raise ERR "parse_term" s

fun parse_entry sexpr = case sexpr of
    Lstring s => string_to_int s
  | _ => raise ERR "parse_entry" ""

fun parse_graph sexpr = case sexpr of
    Lterm l => map parse_entry l
  | Lstring _ => raise ERR "parse_graph" ""

fun parse_line line =
  let
    val sexpr = lisp_parser line
    val (a,b,c,d) = read_info sexpr
  in
    (parse_term c, parse_graph d)
  end

fun parse_setsyntdata () = map parse_line (readl train_file);

(* -------------------------------------------------------------------------
   Bounds on evaluation
   ------------------------------------------------------------------------- *)

val subqlimit = 6
val ilimit = 6
val qlimit = 1000
val qglob = ref 0 

fun assert_ilimit n =
  if length n > ilimit then raise ERR "ilimit" (its ilimit) else () 

fun incrq () =
  (incr qglob; if !qglob > qlimit then raise ERR "incrq" (its qlimit) else ())
fun incrqn n =
  (qglob := !qglob + n; 
   if !qglob > qlimit then raise ERR "incrq" (its qlimit) else ())

(* -------------------------------------------------------------------------
   Ackermann representation
   ------------------------------------------------------------------------- *)

fun nat_to_bin n =
  if n < 0 then raise ERR "" "" else
  if n = 0 then [] else n mod 2 :: nat_to_bin (n div 2)

fun bin_to_nat bin = case bin of
    [] => 0
  | a :: m => a + 2 * bin_to_nat m

fun binel_of bin =
  let
    val l2 = number_snd 0 bin
    val l3 = filter (fn x => fst x = 1) l2
  in
    map (nat_to_bin o snd) l3
  end

fun rm_leadingzeros l = case l of
    [] => []
  | a :: m => if a = 0 then rm_leadingzeros m else l

fun rm_endzeros l = rev (rm_leadingzeros (rev l))

fun binsubq_of n =
  if length (filter (fn x => x = 1) n) > subqlimit 
  then raise ERR "binsubq_of" ""
  else
  let
    val l2 = map (fn x => if x = 1 then [0,1] else [0]) n
    val l3 = cartesian_productl l2
    val l4 = map rm_endzeros l3
  in
    l4
  end

fun pointwise_union l1 l2 = case (l1,l2) of
    ([],_) => l2
  | (_,[]) => l1
  | (a1 :: m1, a2 :: m2) =>
    (if a1 = 1 orelse a2 = 1 then 1 else 0) :: pointwise_union m1 m2

fun pointwise_subset l1 l2 = case (l1,l2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) =>
    (if a1 = 1 andalso a2 = 0 then false else true) andalso
    pointwise_subset m1 m2

fun indexl_to_bin l =
  let
    val maximum = list_imax l
    val d = dset Int.compare l
  in
    List.tabulate (maximum + 1, fn x => if dmem x d then 1 else 0)
  end

(* -------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

val eval_empty = (incrq (); [])

fun eval_sing n = 
  let 
    val _ = (incrq (); assert_ilimit n)
    val i = bin_to_nat n
    val r = List.tabulate (i, fn _ => 0) @ [1] 
  in
     r 
  end

fun eval_binunion (n1,n2) = (incrq (); pointwise_union n1 n2)

fun eval_power n =
  let
    val _ = (incrq (); assert_ilimit n)
    val l1 = map (fn x => if x = 1 then [0,1] else [0]) n
    val l2 = cartesian_productl l1)
    val l3 = map bin_to_nat l2
    val nout = indexl_to_bin l3
  in
    nout
  end

fun eval_term t =
  let
    val (oper,argl) = strip_comb t
    val argle = map eval_term argl
    val s = fst (dest_var oper)
  in
    if hd_string s = #"n"
      then (incrq ();
        (map (string_to_int o Char.toString) (explode (tl_string s))))
    else if term_eq oper tEmpty then eval_empty
    else if term_eq oper tSing
      then eval_sing (singleton_of_list argle)
    else if term_eq oper tbinunion
      then eval_binunion (pair_of_list argle)
    else if term_eq oper tPower
      then eval_power (singleton_of_list argle)
    else raise ERR "eval_term" (term_to_string t)
  end

(* predicates *)
fun eval_equal (n1,n2) = (incrq (); n1 = n2)  

fun eval_in (n1,n2) = 
  (
  incrq (); assert_ilimit n1;
  (List.nth (n2, bin_to_nat n1) = 1 handle Subscript => false)
  ) 

fun eval_sub (n1,n2) = (incrq (); pointwise_subset n1 n2)

fun eval_predicate t =
  let
    val (oper,argl) = strip_comb t
    val r = pair_of_list (map eval_term argl)
  in
    if term_eq oper pEQ          then eval_equal r
    else if term_eq oper pIn     then eval_in r
    else if term_eq oper pSubq   then eval_sub r
    else raise ERR "eval_predicate" (term_to_string t)
  end

(* logical operators and quantifiers *)
fun eval_not b = not b
fun eval_imp (b1,b2) = not b1 orelse b2
fun eval_and (b1,b2) = b1 andalso b2

fun eval_form t =
  if tmem (fst (strip_comb t)) predl then eval_predicate t else
  let
    val (oper,argl) = strip_comb t
    val assocl =
      [(qFORALL_IN,eval_forall_in),(qFORALL_SUBQ,eval_forall_subq),
       (qEXISTS_IN,eval_exists_in),(qEXISTS_SUBQ,eval_exists_subq)]
    val d = dnew Term.compare assocl
  in
    if term_eq oper oNOT
      then eval_not (singleton_of_list (map eval_form argl))
    else if term_eq oper oIMP
      then
        let val (a,b) = pair_of_list argl in
          eval_imp (eval_form a, eval_form b)
        end
    else if term_eq oper oAND
      then
        let val (a,b) = pair_of_list argl in
          eval_and (eval_form a, eval_form b)
        end
    else if tmem oper quantl then
      let val (v,n,t') = triple_of_list argl in
        (dfind oper d) (v, eval_term n, t')
      end
    else raise ERR "eval_form" (term_to_string t)
  end
and eval_subst (v,t) n =
  let val res = mk_var ("n" ^ ilts n, alpha) in
    eval_form (subst [{redex = v, residue = res}] t)
  end
and eval_forall_in (v,n,t) = 
  all (eval_subst (v,t)) (binel_of n)
and eval_forall_subq (v,n,t) = 
  all (eval_subst (v,t)) (binsubq_of n)
and eval_exists_in (v,n,t) = 
  exists (eval_subst (v,t)) (binel_of n)
and eval_exists_subq (v,n,t) =   
  exists (eval_subst (v,t)) (binsubq_of n) 

(* main eval function *)
fun eval_nat t nat = 
  (qglob := 0; eval_subst (xvar,t) (nat_to_bin nat))

fun mk_graph n t = map (eval_nat t) (List.tabulate (n,I))

fun has_graph_aux i graph t = case graph of
    [] => true
  | b :: m => eval_nat t i = b andalso has_graph_aux (i + 1) m t
  
fun has_graph graph t = has_graph_aux 0 graph t

fun graph_to_intl l = map snd (filter fst (number_snd 0 l))

fun eval64 t = 
  SOME (graph_to_intl (mk_graph 64 t)) handle HOL_ERR _ => NONE

(* -------------------------------------------------------------------------
   Synthesis helpers
   ------------------------------------------------------------------------- *)

fun find_redex t = find_term (fn x => is_cont (fst (strip_comb x))) t

val empty_list = listSyntax.mk_nil alpha;

(* -------------------------------------------------------------------------
   Synthesis
   ------------------------------------------------------------------------- *)

val start_form = mk_comb (cont_form, listSyntax.mk_list (xvarl,alpha));

fun res_term move varl =
  if arity_of move <= 0 then move else
  let val arg = mk_comb (cont_term, listSyntax.mk_list (varl,alpha)) in
    list_mk_comb (move, List.tabulate (arity_of move, fn _ => arg))
  end
fun res_logicop move varl =
  let val arg = mk_comb (cont_form, listSyntax.mk_list (varl,alpha)) in
    list_mk_comb (move, List.tabulate (arity_of move, fn _ => arg))
  end
fun res_pred move varl =
  let val arg = mk_comb (cont_term, listSyntax.mk_list (varl,alpha)) in
    if tmem move notpredl
    then
      let
        val x = dfind move notpred_adict
        val argl = List.tabulate (arity_of x, fn _ => arg)
      in
        mk_comb (oNOT, list_mk_comb (x,argl))
      end
    else list_mk_comb (move, List.tabulate (arity_of move, fn _ => arg))
  end
fun res_quant move varl t =
  let
    val qvar = mk_var ("vY" ^ (its (length varl - 1)), alpha)
    val t1 = mk_comb (cont_term, listSyntax.mk_list (varl, alpha))
    val t2 = mk_comb (cont_form, listSyntax.mk_list (qvar :: varl,alpha))
  in
    list_mk_comb (move,[qvar,t1,t2])
  end

fun apply_move_aux move t =
  let
    val red = find_redex t
    val varl = fst (listSyntax.dest_list (rand red))
    val res =
      if type_of red = alpha then
        if is_constr move orelse tmem move varl
          then res_term move varl
        else raise ERR "apply_move_aux" "require term level"
      else if type_of red = bool then
        if is_predmove move then res_pred move varl
        else if is_logicop move then res_logicop move varl
        else if is_quant move then res_quant move varl t
        else raise ERR "apply_move_aux" "require formula level"
      else raise ERR "apply_move_aux" "unexpected type"
  in
    subst_occs [[1]] [{redex = red, residue = res}] t
  end

fun available_move_aux t move =
  let
    val red = find_redex t
    val varl = fst (listSyntax.dest_list (rand red))
  in
    if type_of red = alpha then
      (is_constr move orelse tmem move varl)
    else if type_of red = bool then
      (is_predmove move orelse is_logicop move orelse
      (is_quant move andalso
       length (find_terms is_quant t) < max_quants))
    else false
  end

fun all_applicables t = filter (available_move_aux t) movel;
fun random_step t =
  let val l = all_applicables t in
    if null l then t else apply_move_aux (random_elem l) t
  end

(* -------------------------------------------------------------------------
   Test if moves are enough to recreate the original term
   ------------------------------------------------------------------------- *)

fun topsim (t1,t2) =
  let
    val (oper1,argl1) = strip_comb t1
    val (oper2,argl2) = strip_comb t2
  in
    if term_eq oper1 oper2
    then 1 + sum_int (map topsim (combine (argl1,argl2)))
    else 0
  end

fun imitate_once orgtm tm =
  let
    val movel' = all_applicables tm
    val _ = if null movel'
      then raise ERR "imitate" "no available moves" else ()
    val tml1 = map (fn x => apply_move_aux x tm) movel'
    val tml2 = map_assoc (fn x => topsim (orgtm,x)) tml1
    val tml3 = dict_sort compare_imax tml2
    val newtm = fst (hd tml3)
  in
    if topsim (orgtm,newtm) <= topsim (orgtm,tm)
    then
      (
      print_endline (term_to_string orgtm);
      print_endline (term_to_string tm);
      print_endline (term_to_string newtm);
      print_endline (String.concatWith " " (map term_to_string movel'));
      raise ERR "no progress" ""
      )
    else ();
    newtm
  end

fun imitate orgtm =
  let
    fun loop tm =
      if term_eq orgtm tm then true else loop (imitate_once orgtm tm)
  in
    loop start_form
  end

(*
load "mleSetLib"; open mleSetLib;
load "aiLib"; open aiLib;
val l1 = parse_setsyntdata ();

val l2 = map_assoc (eval64 o fst) l1;
val (l3,l3') = partition (isSome o snd) l2;
val l4 = map_snd valOf l3;
val l5 = map (fn ((a,b),c) => ((a,dict_sort Int.compare b), dict_sort Int.compare c)) l4;
val (l6,l6') = partition (fn ((a,b),c) => b = c) l5;
val l6 = map (fst o fst) l5;
val (l7,l7') = partition (can imitate) l6;
length l3'; length l6'; length l7';

val exl = map fst l1;
fun f ex n = (ignore (eval_nat ex n) handle HOL_ERR _ => qglob := ~1; !qglob);
fun fl ex nl = map (f ex) nl;
val (r,t) = add_time (map_assoc (C fl (List.tabulate (16,I)))) exl;
val (r1,r2) = partition (fn x => exists (fn y => y = ~1) (snd x)) r;
length l1; length r2; t;
val r3 = dict_sort compare_imax (map_snd list_imax r2);
hd (snd (part_n 1000 r3));
*)



end (* struct *)


