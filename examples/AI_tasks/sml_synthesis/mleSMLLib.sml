(* ========================================================================= *)
(* FILE          : mleSMLLib.sml                                             *)
(* DESCRIPTION   : Tools for synthesis of SML programs                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
(* ========================================================================= *)

structure mleSMLLib :> mleSMLLib =
struct

open HolKernel Abbrev boolLib aiLib psTermGen

val ERR = mk_HOL_ERR "mleSMLLib"
val selfdir = HOLDIR ^ "/examples/AI_tasks"

type state = int list list
type instr = string * int * (int list -> int)

(* -------------------------------------------------------------------------
   Kernel functions
   ------------------------------------------------------------------------- *)

fun zero _ = 0
fun suc [x] = x + 1 | suc _ = raise ERR "suc" "" 
fun pred [x] = x - 1 | pred _ = raise ERR "pred" "" 
fun add [a,b] = a + b | add _ = raise ERR "add" "" 
fun diff [a,b] = a - b | diff _ = raise ERR "diff" "" 
fun mult [a,b] = a * b | mult _ = raise ERR "mult" "" 
fun modu [a,b] = a mod b | modu _ = raise ERR "modu" "" 
fun divi [a,b] = a div b | divi _ = raise ERR "divi" ""
fun ife [a,b,c] = if a = 0 then b else c | ife _ = raise ERR "ife" ""
fun ifg [a,b,c] = if a > 0 then b else c | ifg _ = raise ERR "ifg" ""

val namefunl = 
  [("zero",0,zero),
   ("suc",1,suc),("pred",1,pred),
   ("add",2,add),("diff",2,diff),("mult",2,mult),("modu",2,modu),
   ("divi",2,divi),
   ("ife",3,ife),("ifg",3,ifg)]

fun apply_f f x = f x handle Overflow => 0 | Div => 0

(* -------------------------------------------------------------------------
   Execute an instruction
   ------------------------------------------------------------------------- *)

fun exec_instr inputl (name,arity,f) valuel =
  if arity = 0 then map f inputl :: valuel else
  let val (valuel1,valuel2) = part_n arity valuel in
    map (apply_f f) (list_combine valuel1) :: valuel2
  end

fun mk_varinstr varn = ("v" ^ its varn, 0, fn x => List.nth (x,varn))

fun all_input varn maxn = cartesian_productl 
  (List.tabulate (varn, fn _ => List.tabulate (maxn,I)))
fun all_instr varn = List.tabulate (varn, mk_varinstr) @ namefunl

fun random_state inputn staten = List.tabulate (staten, 
  fn _ => shuffle (List.tabulate (inputn,I)))

(*
load "mleSMLLib"; open mleSMLLib;
load "aiLib"; open aiLib;
val varn = 2;
val maxn = 4;
val inputl = all_input varn maxn;
val inputn = length inputl;
val instrl = all_instr varn;
val staten = 3;
val state = random_state inputn staten;
val instr = random_elem instrl;
exec_instr inputl instr state;

today: do everything to be able to code manually fibonacci
*)



end (* struct *)
  
