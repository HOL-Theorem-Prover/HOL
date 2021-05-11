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
val selfdir = HOLDIR ^ "/examples/AI_tasks/sml_synthesis"

(* -------------------------------------------------------------------------
   Kernel functions
   ------------------------------------------------------------------------- *)

type instr = string * int * (int list -> int)

fun zero _ = 0
fun suc [x] = x + 1 | suc _ = raise ERR "suc" "" 
fun pred [x] = x - 1 | pred _ = raise ERR "pred" "" 
fun add [a,b] = a + b | add _ = raise ERR "add" "" 
fun diff [a,b] = a - b | diff _ = raise ERR "diff" "" 
fun mult [a,b] = a * b | mult _ = raise ERR "mult" "" 
fun modu [a,b] = a mod b | modu _ = raise ERR "modu" "" 
fun divi [a,b] = a div b | divi _ = raise ERR "divi" ""

fun relu x = if x >= 0 then x else 0
fun regularize f x = relu (f x) handle Div => 0

val instrl_aux =
  [("zero",0,zero),
   ("suc",1, suc),("pred",1,pred),
   ("add",2,add),("diff",2,diff),("mult",2,mult),("modu",2,modu),
   ("divi",2,divi)]


(*
val instrl_aux =
  [("zero",0,zero),("pred",1,pred),("add",2,add)]
*)

val instrl = map (fn (a,b,c) => (a,b,regularize c)) instrl_aux
val instrd = dnew String.compare (map (fn a => (#1 a, a)) instrl)

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

datatype prog =
    Ins of instr * prog list
  | Test of prog * prog * prog
  | Rec of prog list
  | Proj of int
  | Sub of prog * prog list

exception LocTimeout

fun exec_aux t (mem as (top,input)) argp = 
  if !t <= 0 then raise LocTimeout else 
  (t := !t - 1;
  case argp of
    Ins ((_,_,f),pl) => f (map (exec_aux t mem) pl) 
  | Test (p1,p2,p3) => 
    if exec_aux t mem p1 = 0 then exec_aux t mem p2 else exec_aux t mem p3
  | Rec pl => exec_aux t (top, map (exec_aux t mem) pl) top
  | Proj i => List.nth (input,i)
  | Sub (p,pl) => exec_aux t (p, map (exec_aux t mem) pl) p
  )

fun exec tim prog input = 
  let val t = ref tim in
    SOME (exec_aux t (prog,input) prog) 
  end
  handle Overflow => NONE | LocTimeout => NONE

(* -------------------------------------------------------------------------
   Build a program
   ------------------------------------------------------------------------- *)

datatype bprog =
    BIns of (string * int * (int list -> int))
  | BTest
  | BRec
  | BProj of int
  | BStartSub of int
  | BEndSub;

exception Unbuildable;

fun parterr_aux n acc l =
  if n <= 0 then (rev acc,l) 
  else if null l then raise Unbuildable 
  else parterr_aux (n - 1) (hd l :: acc) (tl l);

fun parterr n l = parterr_aux n [] l;

fun build bins progll = case bins of
    BStartSub arity => (arity,[]) :: progll
  | BEndSub => 
    (case progll of
      (arity1,[prog1]) :: (arity2,progl2) :: cont => 
        let val (a,b) = parterr arity1 progl2 in
          (arity2, Sub (prog1,a) :: b) :: cont
        end
      | _ => raise Unbuildable)
  | _ =>
    (case progll of
      (arity,progl) :: cont => 
      let val newprogl = 
        case bins of
          BIns x => 
          let val (a,b) = parterr (#2 x) progl in
            Ins (x,a) :: b
          end
        | BTest => 
          let val (a,b) = parterr 3 progl in 
            Test (triple_of_list a) :: b
          end
        | BRec => let val (a,b) = parterr arity progl in Rec a :: b end
        | BProj n => (if n >= arity then raise Unbuildable 
                      else Proj n :: progl)
        | _ => raise ERR "build_prog" "match"
      in
        (arity,newprogl) :: cont
      end
    | _ => raise Unbuildable);

end (* struct *)
  
