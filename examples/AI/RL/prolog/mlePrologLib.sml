(* ========================================================================= *)
(* FILE          : mlePrologLib.sml                                          *)
(* DESCRIPTION   : Tools for synthesis of prolog programs                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
(* ========================================================================= *)

structure mlePrologLib :> mlePrologLib =
struct

open HolKernel Abbrev boolLib aiLib psTermGen

val ERR = mk_HOL_ERR "mlePrologLib"
val selfdir = HOLDIR ^ "/examples/AI_tasks"

type prog = (term * term list) list
type table = (term * bool) list

(* -------------------------------------------------------------------------
   Prolog terms
   ------------------------------------------------------------------------- *)

val vi = ref 0

fun rename_varl tm =
  let
    val cache = ref (dempty Term.compare)
    fun rename tm = case dest_term tm of
      VAR(Name,Ty) => (dfind tm (!cache) handle NotFound =>
      let val newtm = mk_var ("V" ^ int_to_string (!vi), Ty) in
        incr vi; cache := dadd tm newtm (!cache); newtm
      end)
    | CONST{Name,Thy,Ty} => tm
    | COMB(Rator,Rand)   => mk_comb (rename Rator,rename Rand)
    | LAMB(Var,Bod) => raise ERR "rename_varl" "abs"
  in
    rename tm
  end

fun renamerule rule =
 swap (strip_imp (rename_varl (list_mk_imp (swap rule))));

exception Break;

fun tryfind f =
   let
      fun F [] = raise ERR "tryfind" "all applications failed"
        | F (h :: t) = f h
        handle Interrupt => raise Interrupt | Break => raise Break | _ => F t
   in
      F
   end

val nref = ref 0

fun backchain rules env goals = case goals of
    [] => env
  | g :: gl =>
    if term_size g > 30 orelse length goals > 30 orelse
       !nref <= 0 then raise Break else
    let
      val _ = nref := !nref - 1
      fun f rule =
      let
        val (w,asm) = renamerule rule
        val newenv = Unify.simp_unify_terms_in_env [] w g env
      in
        backchain rules newenv (asm @ gl)
      end
    in
      tryfind f rules
    end

fun redres_compare (a1,a2) = cpl_compare
  Term.compare Term.compare ((#redex a1, #residue a1),(#redex a2, #residue a2))
fun equal_subst (s1: (term,term) subst,s2 : (term,term) subst) = list_compare redres_compare (s1,s2) = EQUAL;

fun substr sub {redex,residue} = {redex = redex, residue = subst sub residue};

fun solve env =
  let val env' = map (substr env) env in
    if equal_subst (env',env) then env else solve env'
  end

fun execute n prog input =
  let val _ = nref := n in solve (backchain prog [] [input]) end

(* -------------------------------------------------------------------------
   Operators
   ------------------------------------------------------------------------- *)

(*
let sortrules =
 ["sort(X,Y) :- perm(X,Y),sorted(Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;
*)


fun force_const (name,ty) =
  (new_constant (name,ty); mk_const (name,ty))

val nil_tm = listSyntax.nil_tm
val cons_tm = listSyntax.cons_tm
val numsub = [{redex = alpha, residue = ``:num``}]
val nil_num = inst numsub nil_tm
val cons_num = inst numsub cons_tm
val boolsub = [{redex = alpha, residue = ``:bool``}]
val nil_bool = inst boolsub nil_tm
val cons_bool = inst boolsub cons_tm
val rul = force_const ("rul",``:bool -> bool list -> 'a``);
val del = force_const ("del",``:num -> num list -> num list -> bool``);
val leq = force_const ("leq",``:num -> num -> bool``);
val perm = force_const ("perm",``:num list -> num list -> bool``);
val sorted = force_const ("sorted",``:num list -> bool``);
val sort = force_const ("sort",``:num list -> num list -> bool``);

val operlprog = [rul,nil_num,cons_tm,cons_bool,nil_bool]
val operlnum = [numSyntax.zero_tm,numSyntax.suc_tm]
val operllist =  [cons_num, nil_num]
val operlpred = [del,leq,perm,sorted,sort]
val operlall = operlprog @ operlnum @ operllist @ operlpred

val operlsorted = operlprog @ [sorted,leq,nil_num,cons_num]

fun all_var (n1,n2) =
  List.tabulate (n1,fn i => mk_var ("x" ^ its i,``:num``)) @
  List.tabulate (n2,fn i => mk_var ("l" ^ its i,``:num list``))

(* -------------------------------------------------------------------------
   Samples of programs and examples
   ------------------------------------------------------------------------- *)

fun mk_cons x y = listSyntax.mk_cons (x,y)
fun mk_sing x = listSyntax.mk_list ([x],type_of x);
fun mk_del x y z = list_mk_comb (del,[x,y,z])
fun mk_leq x y = list_mk_comb (leq,[x,y])
fun mk_sorted x = mk_comb (sorted,x)

val (x0,x1,x2) = (``x0:num``,``x1:num``,``x2:num``)
val (l0,l1,l2) = ( ``l0:num list``,``l1:num list``,``l2:num list``)
val inputdel = mk_del ``SUC 0`` ``[0; SUC 0]`` ``[0]``

val progdel =
 [(mk_del x0 (mk_cons x0 l0) l0,[]),
  (mk_del x0 (mk_cons x1 l0) (mk_cons x1 l1),[mk_del x0 l0 l1])]
val progleq =
 [(mk_leq ``0`` x0, []),
  (mk_leq ``SUC x0`` ``SUC x1``, [mk_leq x0 x1])]
val progsorted =
 [(mk_sorted nil_num, []),
  (mk_sorted (mk_cons x0 nil_num), []),
  (mk_sorted (mk_cons x0 (mk_cons x1 l0)),
    [mk_leq x0 x1, mk_sorted (mk_cons x1 l0)])
 ]

val cstrdel = ([del,nil_num,cons_num,``SUC``,``0``],bool)
val cstrleq = ([leq,``SUC``,``0``],bool)
val cstrsorted = ([sorted,nil_num,cons_num,``SUC``,``0``],bool)

(* -------------------------------------------------------------------------
   Transform a program term to a list of clauses
   ------------------------------------------------------------------------- *)

fun qt_to_prog qt =
  let
    val l = fst (listSyntax.dest_list qt)
    val hbl = map (pair_of_list o snd o strip_comb) l
  in
    map_snd (fst o listSyntax.dest_list) hbl
  end

fun mk_rul x y = list_mk_comb (rul,[x,y])
fun rule_to_qt (head,body) = mk_rul head (listSyntax.mk_list (body,bool))
fun prog_to_qt prog = listSyntax.mk_list (map rule_to_qt prog,alpha)

(* -------------------------------------------------------------------------
   Generate inputs
   ------------------------------------------------------------------------- *)

val tmoi = numSyntax.term_of_int
fun loi il = listSyntax.mk_list (map tmoi il ,``:num``)

val input_compare = cpl_compare Int.compare (list_compare Int.compare)

fun gen_term_n_aux n (operl,ty) size =
  let val l = gen_term operl (size,ty) in
    if length l >= n
    then first_n n (dict_sort tmsize_compare l)
    else gen_term_n_aux n (operl,ty) (size + 1)
  end

fun gen_term_n (operl,ty) n = gen_term_n_aux n (operl,ty) 1

fun add_output prog input =
  let val b = (ignore (execute 50 prog input); true)
    handle HOL_ERR _ => false
  in
    (input,b)
  end
  handle Break => raise ERR "add_output" "break"

fun create_table_aux prog cstr n =
  let
    val inputl = gen_term_n cstr n
    val iol = map (add_output prog) inputl
    val (pos,neg) = partition snd iol
    val pos' = first_n 40 pos
    val neg' = first_n 20 neg @ random_subset 20 neg
  in
    if length pos' < 10
    then create_table_aux prog cstr (n+100)
    else pos' @ neg'
  end

fun create_table prog cstr = create_table_aux prog cstr 100

(* -------------------------------------------------------------------------
   Test program against known table entries
   ------------------------------------------------------------------------- *)

fun test_io prog (input,output) =
  let val b = (ignore (execute 50 prog input); true)
    handle HOL_ERR _ => false
  in
    (b = output, true)
  end
  handle Break => (false, false)


(*
load "mlePrologLib"; open mlePrologLib;
load "aiLib"; open aiLib;
val table = create_table progdel cstrdel;
val input = fst (List.nth (table,17));
execute 50 progdel input;
val r = map (test_io progdel) table;
*)



end (* struct *)

