(* ========================================================================= *)
(* FILE          : mleSMLLib.sml                                             *)
(* DESCRIPTION   : Tools for synthesis of SML programs                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
(* ========================================================================= *)

structure mleSMLLib :> mleSMLLib =
struct

open HolKernel Abbrev boolLib aiLib mlNeuralNetwork mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleSMLLib"
val selfdir = HOLDIR ^ "/examples/AI_tasks/sml_synthesis"

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type emb = real vector
type instr = string * int * (int list -> int)

datatype move =
    BIns of instr
  | BTest
  | BRec
  | BProj of int
  | BStartSub of int
  | BEndSub

datatype prog =
    Ins of instr * prog list
  | Test of prog * prog * prog
  | Rec of prog list
  | Proj of int
  | Sub of prog * prog list

datatype progl = 
  NilPL of emb | ConsPL of (emb * (emb * prog) * progl) 
fun getemb_progl progl = case progl of
  NilPL emb => emb | ConsPL (emb,_,_) => emb

datatype progll = 
  NilPLL of emb | ConsPLL of (emb * (emb * (int * progl)) * progll)
fun getemb_progll progll = case progll of
  NilPLL emb => emb | ConsPLL (emb,_,_) => emb

type board = int * (emb * int list) * progll
type bareboard = int * int list * (int * prog list) list

(* -------------------------------------------------------------------------
   Global parameters
   ------------------------------------------------------------------------- *)

val maxvar = 1
val natbase = 16

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
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

(* target *)
val nat_cat = mk_var ("nat_cat", rpt_fun_type 3 alpha)
val seq_cat = mk_var ("seq_cat", rpt_fun_type 3 alpha)
fun embv_nat i = mk_var ("nat" ^ its i,alpha)

fun term_of_nat n = 
  if n < 0 then raise ERR "term_of_nat" ""
  else if n < natbase then embv_nat n 
  else list_mk_comb (nat_cat, 
    [embv_nat (n mod natbase), term_of_nat (n div natbase)]);
fun term_of_natl nl =
  case nl of
    [] => raise ERR "term_of_natl" ""
  | [a] => term_of_nat a
  | a :: m => list_mk_comb (seq_cat, [term_of_nat a, term_of_natl m]);

(* program *)
fun embv_proj i = mk_var ("proj" ^ its i, alpha)
val embv_test = mk_var ("test", rpt_fun_type 4 alpha)
fun embv_rec ari = mk_var ("rec" ^ its ari, rpt_fun_type (ari + 1) alpha)
fun embv_instr (name,ari,_) = mk_var (name, rpt_fun_type (ari + 1) alpha)
fun embv_sub ari = mk_var ("sub" ^ its ari, rpt_fun_type (ari + 2) alpha)

fun term_of_prog prog =
  case prog of
    Ins (instr,pl) => list_mk_comb (embv_instr instr, map term_of_prog pl)
  | Test (p1,p2,p3) => list_mk_comb (embv_test, map term_of_prog [p1,p2,p3])
  | Rec pl => list_mk_comb (embv_rec (length pl), map term_of_prog pl)
  | Proj i => embv_proj i
  | Sub (p,pl) => 
    list_mk_comb (embv_sub (length pl), map term_of_prog (p :: pl))





(* board *)
val ol_cat = mk_var ("ol_cat", rpt_fun_type 3 alpha)
fun term_of_board (_,(_,ol),progll) = 
  list_mk_comb (ol_cat, [term_of_natl ol, term_of_progll progll]) 

(* operators *)
val operl_ol = List.tabulate (natbase,embv_nat) @ [nat_cat,seq_cat]

val operl_prog = 
  List.tabulate (maxvar, embv_proj) @ [embv_test] @
  List.tabulate (maxvar + 1, embv_rec) @
  List.tabulate (maxvar + 1, embv_sub) @
  map embv_instr instrl
  


val operl_progll = [progll_nil,progll_cons]

val operl = operl_ol @ operl_prog @ operl_ariprogl @ operl_progll @ [ol_cat]

(* -------------------------------------------------------------------------
   Neural network embedding inference
   ------------------------------------------------------------------------- *)

fun fp_emb tnn oper embl =
  let 
    val inv = Vector.concat embl
    val nn = dfind oper tnn
  in
    #outnv (last (fp_nn nn inv))
  end

fun infer_emb tnn tm =
  let 
    val (oper,argl) = strip_comb tm
    val embl = map (infer_emb tnn) argl 
  in
    fp_emb tnn oper embl
  end

fun reemb_progl tnn prog progl =
  let val outv = fp_emb tnn progl_cons [fst prog, getemb_progl progl] in
    ConsPL (outv, prog, progl)
  end

fun reemb_ariprogl tnn ari progl =
  let 
    val outvari = fp_emb tnn (embv_arity ari) []
    val outv = fp_emb tnn progl_cons [outvari, getemb_progl progl] 
  in
    (outv,(ari,progl))
  end

fun reemb_progll tnn ariprogl progll =
   let val outv = fp_emb tnn progll_cons [fst ariprogl, getemb_progll progll] 
   in
     ConsPLL (outv, ariprogl, progll)
   end

(* -------------------------------------------------------------------------
   Build a program
   ------------------------------------------------------------------------- *)

exception Unbuildable

fun parterr_aux n acc progl = 
  if n <= 0 then (rev acc,progl) else
  case progl of
    NilPL _ => raise Unbuildable
  | ConsPL (_,a,m) => parterr_aux (n - 1) (a :: acc) m

fun parterr n l = parterr_aux n [] l

fun build_progl tnn move (arity,progl) = case move of 
    BIns (instr as (_,ari,_)) => 
    let 
      val (a,b) = parterr ari progl
      val outv = fp_emb tnn (embv_instr instr) (map fst a)
    in
      reemb_progl tnn (outv, Ins (instr,map snd a)) b
    end
  | BTest => 
    let 
      val (a,b) = parterr 3 progl
      val outv = fp_emb tnn embv_test (map fst a)
    in
      reemb_progl tnn (outv, Test (triple_of_list (map snd a))) b
    end
  | BRec => 
    let 
      val (a,b) = parterr arity progl 
      val outv = fp_emb tnn (embv_rec arity) (map fst a)
    in 
      reemb_progl tnn (outv, Rec (map snd a)) b
    end
  | BProj n => if n >= arity then raise Unbuildable else
    let val outv = fp_emb tnn (embv_proj n) [] in 
      reemb_progl tnn (outv, Proj n) progl
    end
  | _ => raise ERR "build_prog" "match"

fun build_progll tnn move progll = case move of
    BStartSub ari => 
    let
      val newprogl1 = NilPL (fp_emb tnn progl_nil [])
      val newprogl2 = reemb_ariprogl tnn ari newprogl1    
    in 
      reemb_progll tnn newprogl2 progll
    end
  | BEndSub => (case progll of
      ConsPLL (_,(_,(ari1,ConsPL (_,prog1,NilPL _))),
        ConsPLL (_,(_,(ari2,progl2)),m)) =>
    let 
      val (a,b) = parterr ari1 progl2 
      val outv = fp_emb tnn (embv_sub ari1) (map fst (prog1 :: a))
      val newprog = (outv, Sub (snd prog1, map snd a))  
      val newprogl = reemb_ariprogl tnn ari2 (reemb_progl tnn newprog b)
    in
      reemb_progll tnn newprogl m
    end
    | _ => raise Unbuildable)
  | _ =>
    (case progll of
      ConsPLL (_,(_,(arity,progl)),m) =>
      let val newprogl =  reemb_ariprogl tnn arity 
        (build_progl tnn move (arity,progl)) 
      in
        reemb_progll tnn newprogl m
      end
    | _ => raise Unbuildable);

(* -------------------------------------------------------------------------
   Test if an instruction can be applied
   ------------------------------------------------------------------------- *)

fun avail_progl move (arity,progl) = case move of 
    BIns (instr as (_,ari,_)) => can (parterr ari) progl
  | BTest => can (parterr 3) progl
  | BRec => can (parterr arity) progl
  | BProj n => n < arity
  | _ => raise ERR "build_prog" "match"

fun avail_progll move progll = case move of
    BStartSub ari => true
  | BEndSub => (case progll of
      ConsPLL (_,(_,(ari1,ConsPL (_,prog1,NilPL _))),
        ConsPLL (_,(_,(ari2,progl2)),m)) =>
      can (parterr ari1) progl2
    | _ => false)
  | _ =>
    (case progll of
      ConsPLL (_,(_,(arity,progl)),m) => avail_progl move (arity,progl)
    | _ => false);

fun avail_board move board = avail_progll move (#3 board)

(* -------------------------------------------------------------------------
   Convert between the two types of board
   ------------------------------------------------------------------------- *)

fun dropemb_progl progl = case progl of
    NilPL emb => []
  | ConsPL (emb,a,m) => snd a :: dropemb_progl m
fun dropemb_progll progll = case progll of
    NilPLL _ => []
  | ConsPLL (_,(_,(ari,progl)),m) => 
    (ari,dropemb_progl progl) :: dropemb_progll m
fun dropemb_board (n,(_,target),progll) = (n,target,dropemb_progll progll)

val emptyemb : real vector = Vector.fromList [] 
fun emptyemb_progl progl = case progl of
    [] => NilPL emptyemb
  | a :: m => ConsPL (emptyemb,(emptyemb,a),emptyemb_progl m)
fun emptyemb_ariprogl (ari,progl) = (emptyemb,(ari,emptyemb_progl progl))
fun emptyemb_progll progll = case progll of
    [] => NilPLL emptyemb
  | a :: m => ConsPLL (emptyemb, emptyemb_ariprogl a, emptyemb_progll m)
fun emptyemb_board (n,ol,progll) = 
  (n,(emptyemb,ol),emptyemb_progll progll)  

fun updemb_progl tnn progl = 
  let val emb = infer_emb tnn (term_of_progl progl) in
    case progl of
      NilPL _ => NilPL emb
    | ConsPL (_,(_,a),m) => 
      let val aemb = infer_emb tnn (term_of_prog a) in 
        ConsPL (emb,(aemb,a), updemb_progl tnn m)
      end
  end
fun updemb_ariprogl tnn (_,(ari,progl)) =
  let val emb = infer_emb tnn (term_of_ariprogl (ari,progl)) in
    (emb, (ari, updemb_progl tnn progl))
  end
fun updemb_progll tnn progll =
  let val emb = infer_emb tnn (term_of_progll progll) in
    case progll of
      NilPLL _ => NilPLL emb
    | ConsPLL (_,a,m) => 
      ConsPLL (emb, updemb_ariprogl tnn a, updemb_progll tnn m)
  end
fun updemb_board tnn (n,(_,ol),progll) =
  let val emb = infer_emb tnn (term_of_natl ol) in
    (n,(emb,ol), updemb_progll tnn progll)
  end


end (* struct *)
  
