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
type ex = (term * term) list

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

fun prettify env = 
  filter (fn x => not (String.isPrefix "V" ((fst o dest_var o #redex) x))) env

fun execute n prog input = 
  let val _ = nref := n in prettify (solve (backchain prog [] [input])) end

(* -------------------------------------------------------------------------
   Operators
   ------------------------------------------------------------------------- *)

val x1 = ``x1:num``;
val x2 = ``x2:num``;
val l1 = ``l1:num list``;
val l2 = ``l2:num list``;
val lr = ``lr:num list``;
val mk_cons = listSyntax.mk_cons
val tysub = [{redex = beta, residue = ``:num list``}];
val numnil = ``[]:num list``;

val prenumcast = ("numcast",``:num list -> 'b``);
val numcastg = (new_constant prenumcast; mk_const prenumcast);
val prenumsing = ("numsing",``:num -> 'b``);
val prenumpair = ("numpair",``:num -> num list -> 'b``);
val numsingg = (new_constant prenumsing; mk_const prenumsing);
val numpairg = (new_constant prenumpair; mk_const prenumpair);

val numsing = inst tysub numsingg
val numpair = inst tysub numpairg
val numcast = inst tysub numcastg;

val numcons = mk_const ("CONS",``:num -> num list -> num list``);
val boolnil = ``[]:bool list``;
val boolcons = mk_const ("CONS",``:bool -> bool list -> bool list``);
val anil = ``[] :'a list``;
val acons = mk_const ("CONS",``:'a -> 'a list -> 'a list``);
val ruler = ("rule",``:bool -> bool list -> 'a``);
val rulec = (new_constant ruler; mk_const ruler);

val delr = ("del",``:num -> 'b -> 'b -> bool``);
val delg = (new_constant delr; mk_const delr);
val del = inst tysub delg;
fun delete x = list_mk_comb (del,x);

val g0 = delete [``3``,``[3;4;5;6]``,lr];

val prog0 = [
 (delete [x1,mk_cons(x1,l1),l1],[]),
 (delete [x1,mk_cons(x2,l1),mk_cons(x2,l2)],[delete [x1,l1,l2]])];

val prog1 = [(delete [x1,mk_cons(x1,l1),l1],[])]

val operl =  
  [delg,x1,x2,l1,l2,numpairg,numcastg,boolnil,boolcons,anil,acons,rulec];

val operl_novar =
  [delg,numpairg,numcastg,boolnil,boolcons,acons,rulec];

fun operl_nn (n1,n2) = 
  operl_novar @ 
  List.tabulate (n1,fn i => mk_var ("x" ^ its i,``:num``)) @
  List.tabulate (n2,fn i => mk_var ("l" ^ its i,``:num list``))

(* -------------------------------------------------------------------------
   Generate prolog programs
   ------------------------------------------------------------------------- *)

fun random_qt size = random_term operl (size,``:'a list``);
fun random_qtl size n = random_terml operl(size,``:'a list``) n;

fun subst_singpair tm = 
  let 
    val (oper,argl) = strip_comb tm 
    val newargl = map subst_singpair argl
  in
    if tmem oper [numsing] then listSyntax.mk_list (newargl, ``:num``)
    else if tmem oper [numpair] then listSyntax.mk_cons (pair_of_list newargl)
    else if tmem oper [numcast] then (singleton_of_list newargl)
    else list_mk_comb (oper,newargl)  
  end;

fun qt_to_prog qt =
  let 
    val qt' = subst_singpair (inst tysub qt)
    val l = fst (listSyntax.dest_list qt')
    val hbl = map (pair_of_list o snd o strip_comb) l
  in
    map_snd (fst o listSyntax.dest_list) hbl
  end

(* -------------------------------------------------------------------------
   Generate examples exhaustively
   ------------------------------------------------------------------------- *)

val tmoi = numSyntax.term_of_int
fun loi il = listSyntax.mk_list (map tmoi il ,``:num``)

val input_compare = cpl_compare Int.compare (list_compare Int.compare) 

fun all_input (siz,len) = 
  let 
    val numberl = List.tabulate (siz,I)
    val inputl1 = 
      let fun f n = cartesian_productl (List.tabulate (n, fn _ => numberl)) in
        List.concat (List.tabulate (len,f))
      end
    val inputl2 = 
      let fun f l = map (fn x => (x,l)) l in
        List.concat (map f inputl1)
      end
  in
    mk_fast_set input_compare inputl2
  end

fun create_ex prog (a,b) =
  let 
    val input = delete [tmoi a,loi b,lr]
    val env = execute 50 prog input 
    val output = subst env lr
  in
    (input,output)
  end;

fun all_ex prog (siz,len) =
  map (create_ex prog) (all_input (siz,len))

(* -------------------------------------------------------------------------
   Test program on examples
   ------------------------------------------------------------------------- *)

fun test_unit prog (input,output) = 
  let val b = term_eq (subst (execute 20 prog input) lr) output in 
    (b, b)
  end
  handle Interrupt => raise Interrupt 
  | Break => (false, false)
  | _ => (false, true)

(*
load "mlePrologLib"; open mlePrologLib;
load "aiLib"; open aiLib;
val exl = all_ex prog0 (2,3);
val ex = List.nth (exl,13);
val r = map (test_unit prog1) exl;
*)



end (* struct *)

