(* ========================================================================= *)
(* FILE          : mleSMLLib.sml                                             *)
(* DESCRIPTION   : Tools for synthesis of SML programs                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
(* ========================================================================= *)

structure mleSMLLib :> mleSMLLib =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "mleSMLLib"
val selfdir = HOLDIR ^ "/examples/AI_tasks/sml_synthesis"

(* -------------------------------------------------------------------------
   Global parameters
   ------------------------------------------------------------------------- *)

val natbase = 16
val maxvar = 1
val maxstep = 30

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type instr = string * int * (int list -> int)

datatype prog =
    Ins of instr * prog list
  | Test of prog * prog * prog
  | Rec of prog list
  | Proj of int
  | Sub of prog * prog list

datatype move =
  BIns of instr | BTest | BRec | BProj of int | BSub of int | BEndSub;

type board = int * int list * (int * prog list) list

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)

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

val instrl = map (fn (a,b,c) => (a,b,regularize c)) instrl_aux
val instrd = dnew String.compare (map (fn a => (#1 a, a)) instrl)

(* -------------------------------------------------------------------------
   Print a program
   ------------------------------------------------------------------------- *)

fun string_of_prog prog =
  let
    fun s_x n = "x" ^ its n
    fun s_xl n = "(" ^ String.concatWith "," (List.tabulate (n,s_x)) ^ ")"
    fun s_f d = "f" ^ its d
    fun s_p d ptop = case ptop of
      Ins ((name,_,_),pl) =>
      if name = "zero" then "0" else name ^ s_al d pl
    | Test (p1,p2,p3) => String.concatWith " "
      ["if", s_p d p1, "= 0 then", s_p d p2, "else", s_p d p3]
    | Rec pl => s_f d ^ s_al d pl
    | Proj n => s_x n
    | Sub (p,pl) => String.concatWith " "
      ["let fun", s_f (d+1) ^ s_xl (length pl), "=",
       s_p (d+1) p, "in", s_f d ^ s_al d pl, "end"]
    and s_al d pl =
     "(" ^ String.concatWith "," (map (s_p d) pl) ^ ")"
  in
    s_p 0 prog
  end

fun string_of_ariprogl (ari,progl) =
  "#" ^ its ari ^ " " ^
  String.concatWith "\n#~ " (map string_of_prog progl)

fun string_of_progll progll =
  String.concatWith "\n" (map string_of_ariprogl progll)

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

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

exception Unbuildable

fun parterr_aux n acc l =
  if n <= 0 then (rev acc,l)
  else if null l then raise Unbuildable
  else parterr_aux (n - 1) (hd l :: acc) (tl l);

fun parterr n l = parterr_aux n [] l;

fun longer_than n l =
  if n <= 0 then true
  else if null l then false
  else longer_than (n-1) (tl l)

fun build move progll = case move of
    BSub arity => (arity,[]) :: progll
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
        case move of
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

fun available (_,_,progll) move = case move of
    BSub arity => true
  | BEndSub =>
    (case progll of
      (arity1,[prog1]) :: (arity2,progl2) :: cont =>
       longer_than arity1 progl2
      | _ => false)
  | _ =>
    (case progll of
      (arity,progl) :: cont =>
      (case move of
        BIns x => longer_than (#2 x) progl
      | BTest => longer_than 3 progl
      | BRec => longer_than arity progl
      | BProj n => n < arity
      | _ => raise ERR "available" "match")
    | _ => false)


(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

(* target *)
val nat_cat = mk_var ("nat_cat", rpt_fun_type 3 alpha)
val seq_cons = mk_var ("seq_cons", rpt_fun_type 3 alpha)
fun embv_nat i = mk_var ("nat" ^ its i,alpha)
val operl_ol = List.tabulate (natbase,embv_nat) @ [nat_cat, seq_cons]

fun term_of_nat n =
  if n < 0 then raise ERR "term_of_nat" ""
  else if n < natbase then embv_nat n
  else list_mk_comb (nat_cat,
    [embv_nat (n mod natbase), term_of_nat (n div natbase)])
fun term_of_natl nl =
  case nl of
    [] => raise ERR "term_of_natl" ""
  | [a] => term_of_nat a
  | a :: m => list_mk_comb (seq_cons, [term_of_nat a, term_of_natl m])

(* program *)
fun embv_proj i = mk_var ("proj" ^ its i, alpha)
val embv_test = mk_var ("test", rpt_fun_type 4 alpha)
fun embv_rec ari = mk_var ("rec" ^ its ari, rpt_fun_type (ari + 1) alpha)
fun embv_instr (name,ari,_) = mk_var (name, rpt_fun_type (ari + 1) alpha)
fun embv_sub ari = mk_var ("sub" ^ its ari, rpt_fun_type (ari + 2) alpha)
val operl_prog =
  List.tabulate (maxvar, embv_proj) @ [embv_test] @
  List.tabulate (maxvar + 1, embv_rec) @
  List.tabulate (maxvar + 1, embv_sub) @
  map embv_instr instrl

fun term_of_prog prog =
  case prog of
    Ins (instr,pl) => list_mk_comb (embv_instr instr, map term_of_prog pl)
  | Test (p1,p2,p3) => list_mk_comb (embv_test, map term_of_prog [p1,p2,p3])
  | Rec pl => list_mk_comb (embv_rec (length pl), map term_of_prog pl)
  | Proj i => embv_proj i
  | Sub (p,pl) =>
    list_mk_comb (embv_sub (length pl), map term_of_prog (p :: pl))

(* program stack *)
val progl_nil = mk_var ("progl_nil", alpha)
val progl_cons = mk_var ("progl_cons", rpt_fun_type 3 alpha)
fun embv_arity ari = mk_var ("arity" ^ its ari,alpha)
val arity_cat = mk_var ("arity_cat", rpt_fun_type 3 alpha)
val operl_ariprogl =
  [progl_nil,progl_cons,arity_cat] @
  List.tabulate (maxvar + 1, embv_arity)

fun term_of_progl progl = case progl of
    [] => progl_nil
  | a :: m => list_mk_comb (progl_cons,[term_of_prog a,term_of_progl m])

fun term_of_ariprogl (ari,progl) =
  list_mk_comb (arity_cat, [embv_arity ari, term_of_progl progl])

(* program stack stack *)
val progll_cons = mk_var ("progll_cons", rpt_fun_type 3 alpha)

fun term_of_progll progll = case progll of
    [] => raise ERR "term_of_progll" ""
  | [a] => term_of_ariprogl a
  | a :: m =>
    list_mk_comb (progll_cons,[term_of_ariprogl a,term_of_progll m])

(* board *)
val ol_cat = mk_var ("ol_cat", rpt_fun_type 3 alpha)

fun term_of_board (_,ol,progll) =
  list_mk_comb (ol_cat, [term_of_natl ol, term_of_progll progll])

val operl = operl_ol @ operl_prog @ operl_ariprogl @ [progll_cons, ol_cat]

(* heads *)
val head_eval = mk_var ("head_eval", rpt_fun_type 2 alpha)
val head_poli = mk_var ("head_poli", rpt_fun_type 2 alpha)

fun tob board =
  let val tm = term_of_board board in
    [mk_comb (head_eval,tm), mk_comb (head_poli,tm)]
   end


end (* struct *)

