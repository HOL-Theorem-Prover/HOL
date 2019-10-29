(* ========================================================================= *)
(* FILE          : mleSetEval.sml                                            *)
(* DESCRIPTION   : Library for synthesis of formulas in Set Theory           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSetLib :> mleSetLib =
struct

open HolKernel Abbrev boolLib aiLib mleLib
val ERR = mk_HOL_ERR "mleSetLib"

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
val pIN = mk_var ("pIN", binpred)
val pNOTIN = mk_var ("pNOTIN", binpred)
val pSUB = mk_var ("pSUB", binpred)
val pNOTSUB= mk_var ("pNOTSUB", binpred)
val predl = [pEQ,pIN,pNOTIN,pSUB,pNOTSUB]
fun is_pred t = tmem t predl;

val oNOT = mk_var ("oNOT", ``:bool -> bool``)
val oIMP = mk_var ("oIMP", ``:bool -> bool -> bool``)
val oOR = mk_var ("oOR", ``:bool -> bool -> bool``)
val logicopl = [oNOT,oIMP,oOR]
fun is_logicop t = tmem t logicopl

val quant_type = ``:'a -> 'a -> bool -> bool``
val qFORALL_IN = mk_var ("qFORALL_IN",quant_type)
val qFORALL_SUBQ = mk_var ("qFORALL_IN",quant_type)
val qEXISTS_IN = mk_var ("qEXISTS_IN",quant_type)
val qEXISTS_SUBQ = mk_var ("qEXISTS_SUBQ",quant_type)
val quantl = [qFORALL_IN,qFORALL_SUBQ,qEXISTS_IN,qEXISTS_SUBQ]
fun is_quant t = tmem t quantl;

val maximum_vars = 4;
val yvarl = List.tabulate (maximum_vars, fn i => mk_var ("Y" ^ its i,alpha));
val xvar = mk_var ("X",alpha);
val xvarl = [xvar];
val cont_term = mk_var ("cont_term",``:'a list -> 'a``);
val cont_form = mk_var ("cont_form", ``:'a list -> bool``);
fun is_cont t = tmem t [cont_term,cont_form];

(* -------------------------------------------------------------------------
   Helpers
   ------------------------------------------------------------------------- *)

fun nat_to_bin n =
  if n < 0 then raise ERR "" "" else
  if n <= 1 then [n] else n mod 2 :: nat_to_bin (n div 2)
fun bin_to_nat bin = case bin of
    [] => 0
  | a :: m => a + 2 * bin_to_nat m

fun nat_to_indexl n = 
  let 
    val l1 = nat_to_bin n 
    val l2 = number_snd 0 l1
    val l3 = filter (fn x => fst x = 1) l2
  in
    map snd l3
  end

fun mk_sing a = mk_comb (tSing,a)

(* 
fun nat_to_finset n = 
  case map (mk_sing o nat_to_finset) (nat_to_indexl n) of
    [] => tEmpty
  | l => list_mk_binop tbinunion l
*)

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

(* terms *)
val constructorl = [tEmpty,tSing,tbinunion,tPower];
val eval_limit = 128
val eval_empty = 0

fun eval_sing n = 
  let val r = int_pow 2 n in
    if r >= eval_limit then raise ERR "eval_sing" "" else r
  end

fun eval_binunion (n1,n2) =
  let 
    val (l1,l2) = (nat_to_bin n1, nat_to_bin n2) 
    val r = bin_to_nat (pointwise_union l1 l2)
  in
    if r >= eval_limit then raise ERR "eval_binunion" "" else r
  end

fun eval_power n =
  let 
    val l1 = nat_to_bin n
    val l2 = map (fn x => if x = 1 then [0,1] else [0]) l1
    val l3 = cartesian_productl l2
    val l4 = map bin_to_nat l3
    val r = bin_to_nat (indexl_to_bin l4)
  in
    if r >= eval_limit then raise ERR "eval_power" "" else r
  end

fun eval_power_exempt n =
  let 
    val l1 = nat_to_bin n
    val l2 = map (fn x => if x = 1 then [0,1] else [0]) l1
    val l3 = cartesian_productl l2
    val l4 = map bin_to_nat l3
    val r = bin_to_nat (indexl_to_bin l4)
  in
    r
  end

fun hd_string s = String.sub (s,0)
fun tl_string s = String.substring (s, 1, String.size s - 1)

fun eval_term t = 
  let 
    val (oper,argl) = strip_comb t 
    val argle = map eval_term argl
    val s = fst (dest_var oper)
  in
    if hd_string s = #"n" 
      then string_to_int (tl_string s)
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
val predl = [pEQ,pIN,pNOTIN,pSUB,pNOTSUB];
fun eval_equal (n1,n2) = n1 = n2
fun eval_in (n1,n2) = 
  List.nth (nat_to_bin n2,n1) = 1 handle Subscript => false
fun eval_notin (n1,n2) = not (eval_in (n1,n2))
fun eval_sub (n1,n2) = 
  let val (l1,l2) = (nat_to_bin n1, nat_to_bin n2) in
    pointwise_subset l1 l2
  end
fun eval_notsub (n1,n2) = not (eval_sub (n1,n2))

fun eval_predicate t =
  let 
    val (oper,argl) = strip_comb t
    val r = pair_of_list (map eval_term argl)
  in
    if term_eq oper pEQ          then eval_equal r
    else if term_eq oper pIN     then eval_in r
    else if term_eq oper pNOTIN  then eval_notin r
    else if term_eq oper pSUB    then eval_sub r
    else if term_eq oper pNOTSUB then eval_notsub r
    else raise ERR "eval_predicate" (term_to_string t)
  end

(* logical operators *)
val operatorl = [oNOT,oIMP,oOR]
val quantl = [qFORALL_IN,qFORALL_SUBQ,qEXISTS_IN,qEXISTS_SUBQ]

fun eval_not b = not b
fun eval_imp (b1,b2) = not b1 orelse b2
fun eval_or (b1,b2) = b1 orelse b2

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
      then eval_imp (pair_of_list (map eval_form argl))
    else if term_eq oper oOR 
      then eval_or (pair_of_list (map eval_form argl))
    else if tmem oper quantl then 
      let val (v,n,t') = triple_of_list argl in
        (dfind oper d) (v,eval_term n,t')
      end
    else raise ERR "eval_form" (term_to_string t)
  end
and eval_subst (v,t) n' =
  let val res = mk_var ("n" ^ its n',alpha) in
    eval_form (subst [{redex = v, residue = res}] t)
  end
and eval_forall_in (v,n,t) =
  all (eval_subst (v,t)) (nat_to_indexl n)
and eval_forall_subq (v,n,t) =
  all (eval_subst (v,t)) (nat_to_indexl (eval_power_exempt n))    
and eval_exists_in (v,n,t) =
  exists (eval_subst (v,t)) (nat_to_indexl n)
and eval_exists_subq (v,n,t) =
  exists (eval_subst (v,t)) (nat_to_indexl (eval_power_exempt n))  

(* -------------------------------------------------------------------------
   Synthesis helpers
   ------------------------------------------------------------------------- *)

fun find_qvar t =
  let 
    fun test x = is_var x andalso hd_string (fst (dest_var x)) = #"Y"
    val varl = find_terms test t
    val nl = map (string_to_int o tl_string o fst o dest_var) varl
    val nmax = if null nl then ~1 else list_imax nl
    val _ = if nmax >= maximum_vars then raise ERR "find_qvar" "" else () 
  in
    mk_var ("Y" ^ its (nmax + 1),alpha)
  end
fun find_redex t = find_term (fn x => is_cont (fst (strip_comb x))) t

val empty_list = listSyntax.mk_nil alpha;

(* -------------------------------------------------------------------------
   Synthesis
   ------------------------------------------------------------------------- *)

val start_form = mk_comb (cont_form, listSyntax.mk_list (xvarl,alpha));

fun res_term move varl =
  if arity_of move <= 0 then move else
  let 
    val newvarl = filter (fn x => not (term_eq x xvar)) varl
    val arg = mk_comb (cont_term, listSyntax.mk_list (newvarl,alpha))
  in
    list_mk_comb (move, List.tabulate (arity_of move, fn _ => arg))
  end
fun res_logicop move varl =
  let val arg = mk_comb (cont_form, listSyntax.mk_list (varl,alpha)) in
    list_mk_comb (move, List.tabulate (arity_of move, fn _ => arg))
  end
fun res_pred move varl =
  let val arg = mk_comb (cont_term, listSyntax.mk_list (varl,alpha)) in
    list_mk_comb (move, List.tabulate (arity_of move, fn _ => arg))
  end
fun res_quant move varl t =
  let 
    val qvar = find_qvar t
    val t1 = mk_comb (cont_term, listSyntax.mk_list (xvarl,alpha))
    val t2 = mk_comb (cont_form, listSyntax.mk_list (qvar :: varl,alpha)) 
  in
    list_mk_comb (move,[qvar,t1,t2])
  end

fun apply_move move t = 
  let 
    val red = find_redex t
    val varl = fst (listSyntax.dest_list (rand red))
    val res = 
      if type_of red = alpha then
        if is_constr move orelse tmem move varl
          then res_term move varl
        else raise ERR "apply_move" "require term level"
      else if type_of red = bool then
        if is_pred move then res_pred move varl
        else if is_logicop move then res_logicop move varl
        else if is_quant move then res_quant move varl t
        else raise ERR "apply_move" "require formula level"
      else raise ERR "apply_move" "unexpected type"
  in
    subst_occs [[1]] [{redex = red, residue = res}] t
  end

(*
val t1 = apply_move qFORALL_IN start_form;
val t2 = apply_move tPower t1;
val t3 = apply_move tEmpty t2;
val t4 = apply_move tEmpty t3;
*)

val movel = constrl @ predl @ logicopl @ quantl @ xvarl @ yvarl;
fun is_applicable t move = can (apply_move move) t;
fun all_applicables t = filter (is_applicable t) movel;
fun random_step t =
  let val l = all_applicables t in
    if null l then t else apply_move (random_elem l) t   
  end

(* -------------------------------------------------------------------------
   Printing to sexpr
   ------------------------------------------------------------------------- *)

(*
load "mleSetLib"; open mleSetLib;
load "aiLib"; open aiLib;
val formula = (funpow 20 random_step) start_form;

val r = if can (find_term is_cont) formula
        then NONE 
        else SOME (map (eval_subst (xvar,formula)) (List.tabulate (16,I)));
*)

(*
fun rename s = 
  let 
    fun f c = if c = #"_" then "-" else Char.toString c
    val s1 = String.translate f s
  in
    String.substring (s1, 1, String.size s1 - 1)
  end
*)

end (* struct *)


