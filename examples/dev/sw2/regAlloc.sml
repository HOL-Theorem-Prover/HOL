structure regAlloc :> regAlloc =
struct

open HolKernel Parse boolLib bossLib ;
open pairLib pairSyntax PairRules NormalTheory Normal basic;

(* --------------------------------------------------------------------*)
(* --------------------------------------------------------------------*)

structure M = Binarymap
structure S = Binaryset
val N = numSyntax.num;

(* --------------------------------------------------------------------*)
(* Datatypes                                                           *)
(* --------------------------------------------------------------------*)

datatype alloc_result =
    Alloc of term (* allocated register *)
  | Spill of term (* spilled variable *)

(* --------------------------------------------------------------------*)
(* Pre-defined variables and functions                                 *)
(* --------------------------------------------------------------------*)

val DEBUG = ref true;

val allregs = map Term [`r0:num`, `r1:num`,  `r2:num`,  `r3:num`,  
                        `r4:num`, `r5:num`,  `r6:num`,  `r7:num`,  `r8:num`]
val reg_sp = ``r13:num`` (* stack pointer *)
val reg_hp = ``r9:num``  (* heap pointer  *)

fun is_reg x = (String.sub (term_to_string x,0) = #"r")
fun is_mem x = (String.sub (term_to_string x,0) = #"m")

fun num2name stem i = stem ^ Lib.int_to_string i
val mStrm = ref (Lib.mk_istream (fn x => x+1) 0 (num2name "m"))
val tStrm = Lib.mk_istream (fn x => x+1) 0 (num2name "t")

fun reset_mvar () = mStrm := Lib.mk_istream (fn x => x+1) 0 (num2name "m")
fun next_mvar () = mk_var (state(next (!mStrm)), N)
fun next_tvar () = mk_var (state(next tStrm), N)

fun fv exp = 
  let val xs = free_vars exp
      val xs' = List.filter (fn x => not (is_mem x orelse is_reg x)) xs
  in  xs'
  end

fun tvarOrder (t1:term,t2:term) =
  let val (s1,s2) = (term_to_string t1, term_to_string t2) in
    if s1 > s2 then GREATER
    else if s1 = s2 then EQUAL
    else LESS
  end;

fun is_fun exp = 
  is_var exp andalso 
  (#1 (dest_type (type_of exp)) = "fun")
  handle _ => false;

(* --------------------------------------------------------------------*)
(* Attempt to allocate a register                                      *)
(* --------------------------------------------------------------------*)

(* allocate a register or spill a variable *)

val regL = ref [Term `r0:num`, Term `r1:num`, Term `r2:num`, Term `r3:num`];

fun alloc cont regenv x =
  let val all = !regL (* allregs *) in
    if is_reg x then Alloc(x) else
    let 
      val free = fv cont
      val live =    (* the set of registers already assigned to those live variables in cont *)
        List.foldl
          (fn (y,live) =>
            if is_reg y then S.add (live,y) else       (* registers to be used *)
              S.add (live, M.find (regenv, y))         (* registers (and memory) already assigned *) 
                handle NotFound => live)
          (S.empty tvarOrder)
          free
      val candidate =  (* the first available register *)
        List.find
          (fn r => not (S.member(live,r)))
          all
    in
       case candidate of
         SOME r => Alloc(r)
       | NONE => 
           let val y = valOf (
              List.find
              (fn y =>
                 let val k = M.find(regenv,y) in
                   not (is_reg y) andalso             (* exclude variables that are in registers *)
                   not (is_mem k) andalso             (* exclude spilled variables (in memory) *) 
                  (List.exists (fn z => (k = z)) all) (* made sure that it has been assigned a register *)
                  end
                  handle NotFound => false)
             (List.rev free))
               val _ = if !DEBUG then 
                  (print ("register allocation failed for " ^ (term_to_string x) ^ "; ");
                   print ("spilling " ^ (term_to_string y) ^ " from " ^ (term_to_string (M.find(regenv,y))) ^ "\n"))
                  else ()
           in
             Spill(y)
           end
     end
  end

(* --------------------------------------------------------------------*)
(* Register Allocation                                                 *)
(* Auxiliary data structures and functions                             *)
(* --------------------------------------------------------------------*)

datatype g_result =
    NoSpill of term * (term, term) M.dict (* new regenv *)
  | ToSpill of term * term list           (* spilled variables *)

exception regAlloc of string
exception NoReg of term

fun find_reg (regenv,x) =
  if is_reg x then x else
  let val v = M.find (regenv, x) in
    if is_reg v then v
    else raise (NoReg x)
  end
  handle NotFound => raise (NoReg x)

fun mk_subst_rules xs regenv =
    List.foldl
      (fn (x,ys) =>
        if is_var x then (x |-> find_reg (regenv, x)) :: ys
        else ys)
      []
      xs;

fun concat e1 x e2 = 
  if is_let e1 then 
    let val (v,M,N) = dest_plet e1 in
        mk_plet (v, M, concat N x e2)
    end
  else 
    mk_plet (x, e1, e2)

fun add x r regenv =
  if is_reg x then regenv
  else M.insert(regenv, x, r)

fun list_mem x xs = 
  not ((List.find (fn k => (k = x)) xs) = NONE)

(* --------------------------------------------------------------------*)
(* Spill to memory                                                     *)
(* Restore from memory                                                  *)
(* --------------------------------------------------------------------*)

fun save x exp regenv =
  let val v = next_mvar ()
      val regenv1 = M.insert(regenv, x, v)    (* x is spilled to memory *)
      val _ = if !DEBUG then 
                print ("saving " ^ term_to_string x ^ " to " ^ term_to_string v ^"\n")
               else ()
  in 
     (mk_plet (v, M.find(regenv,x), exp), regenv1)   (* let m[.] = r[.] in exp *)
  end

fun restore x exp regenv =
  let val v = next_tvar ()
      val _ = if !DEBUG then 
                print ("restoring " ^ term_to_string x ^ " from " ^ term_to_string (M.find(regenv,x)) ^"\n")
               else ()
  in mk_plet (v, M.find (regenv,x), 
          subst_exp [x |-> v] exp)    (* let v = m[.] in exp[x <- v] *)
  end

(* --------------------------------------------------------------------*)
(* Register Allocation                                                 *)
(* Main algorithm                                                      *)
(* --------------------------------------------------------------------*)

fun g' dest cont regenv exp =
  if is_word_literal exp orelse numSyntax.is_numeral exp orelse is_const exp orelse 
     is_fun exp orelse is_mem exp then NoSpill (exp, regenv)
  else if is_var exp then NoSpill (subst (mk_subst_rules [exp] regenv) exp, regenv)
  else if is_cond exp then
    let val (c,e1,e2) = dest_cond exp
        val (cmpop,ds) = strip_comb c
        val (d0,d1) = (hd ds, hd (tl ds))
        val c' = list_mk_comb (cmpop, [find_reg (regenv,d0), find_reg (regenv,d1)])
        fun f e1 e2 = mk_cond(c', e1, e2)
    in
        g'_if dest cont regenv exp f e1 e2
    end
  else if is_comb exp then
    let val (op0,xs) = strip_comb exp in
      if is_binop op0 orelse is_cmpop op0 orelse is_relop op0 then
        let val (x, y) = (hd xs, hd (tl xs))
        in NoSpill (subst (mk_subst_rules [x,y] regenv) exp, regenv)
        end
      else raise regAlloc ("g': this case hasn't been unimplemented -- " ^ term_to_string exp)
    end
  else NoSpill (exp, regenv)

and

(* fun *) g'_and_restore dest cont regenv exp =
  g' dest cont regenv exp
  handle NoReg x =>                           (* x is stored in the memory, need to be assigned a register *)
      g dest cont regenv (restore x exp regenv)    (* restore the spilled x from the memory *)

and

 g dest cont regenv exp = 
  if is_let exp then                        (*  exp = LET (\v. N) M  *)
     let
       val (x,M,N) = dest_plet exp
       val cont' = concat N dest cont
     in
       if is_mem x then 
          case (g x cont regenv N) of
               ToSpill(e2, ys) =>
                 ToSpill (exp, ys)
            |  NoSpill(e2, regenv2) => NoSpill(mk_plet(x,M,e2), regenv2)
       else
       case g'_and_restore x cont' regenv M of
            ToSpill(e1, ys) => ToSpill(concat e1 x N, ys)
         |  NoSpill(e1', regenv1) =>
            ( case (alloc cont' regenv1 x) of
                 Spill(y) => ToSpill (mk_plet(x,M,N), [y])       (* ToSpill(Let(x, M, Forget(y, N)), [y]) *)
              |  Alloc(r) =>
                 ( case (g dest cont (add x r regenv1) N) of
                     ToSpill(e2, ys) => 
                       if list_mem x ys then
                          let val (e',regenv') = save x e2 (add x r regenv1)
                              val x_saved = concat e1' r e' in
			    (case List.filter (fn y => y <> x) ys of
			          []      => g dest cont regenv' x_saved
			       |  ys_left => ToSpill(x_saved, ys_left))
                          end
                       else
                         ToSpill (mk_plet(x,M,N), ys)
                  |  NoSpill(e2', regenv2) => NoSpill(concat e1' r e2', regenv2)
                 )
            )
     end
  else
     g'_and_restore dest cont regenv exp
 
and

(*fun*) g'_if dest cont regenv exp constr e1 e2 =
  let 
    val (e1', regenv1) = g_repeat dest cont regenv e1
    val (e2', regenv2) = g_repeat dest cont regenv e2
    val regenv' =
      List.foldl
      (fn (x,regenv') =>
          if is_reg x then regenv' else
          let val r1 = M.find(regenv1,x)
              val r2 = M.find(regenv2,x) in
            if r1 <> r2 then regenv' else
            M.insert(regenv',x,r1)
          end
        handle NotFound => regenv')
      (M.mkDict tvarOrder)
      (fv cont)
  in
    case
      List.filter
      (fn x => not (is_reg x) andalso (M.peek(regenv',x) = NONE) andalso x <> dest)
      (fv cont)
    of 
      [] => NoSpill(constr e1' e2', regenv')
    | xs => ToSpill(exp, xs)
  end

and

(* fun *) g_repeat dest cont regenv exp =
   case g dest cont regenv exp of
      NoSpill(exp', regenv') => (exp', regenv')
    | ToSpill(exp, xs) =>
        let val (exp',regenv') = 
              List.foldl
               (fn (x,(exp,env)) => save x exp env)
               (exp, regenv)
               xs
        in
          g_repeat dest cont regenv' exp'
        end

(*
  The caller-save convention (where every function call is assumed to destroy the values
  of all registers) requires us to save the values of all registers that are live at the 
  point of making a function call
*)

fun g'_call dest cont regenv exp constr ys =
  case
    List.filter
      (fn x => not (is_reg x) andalso x <> dest)
      (fv cont)
  of [] => NoSpill (constr (List.map (fn y => find_reg(regenv, y)) ys),
                    M.mkDict tvarOrder)
   | xs => ToSpill(exp, xs)

(* --------------------------------------------------------------------*)
(* Register Allocation                                                 *)
(* --------------------------------------------------------------------*)

fun args_env args = 
   let val argL = strip_pair args
       fun assgn_v (v,(i,regenv)) = 
            (i+1, M.insert (regenv, v, mk_var ("r" ^ Int.toString i, N)))
   in
       #2 (List.foldl assgn_v (0, M.mkDict tvarOrder) argL)
   end

fun assgn_args args regenv = 
  let 
    val argL = strip_pair args
    fun mk_rules xs regenv =
      List.foldl
        (fn (x,ys) =>
          if is_var x then (x |-> M.find (regenv, x)) :: ys
          else ys)
        []
        xs
  in
    subst (mk_rules (strip_pair args) regenv) args
  end

fun alloc_mem tm =
  let
     fun trav t env =
       if is_let t then
           let val (v,M,N) = dest_plet t
           in 
              if is_mem v then
                let val v' = next_mvar ()
                    val M' = mk_comb (inst [alpha |-> type_of M] ``save``, M)
                    val env' = M.insert (env, v, v')
                    val N' = trav N env'
                in
                    mk_plet (v', M', N')
                end
              else if is_var M andalso is_mem M then
                let val M' = mk_comb (inst [alpha |-> type_of M] ``loc``, M.find (env, M))
                    val N' = trav N env
                in
                    mk_plet (v, M', N')
                end
              else mk_plet (v, trav M env, trav N env)
            end
       else if is_comb t then
            let val (M1,M2) = dest_comb t
                val M1' = trav M1 env
                val M2' = trav M2 env
            in mk_comb(M1',M2')
            end
       else t
  in
    (reset_mvar ();
     trav tm (M.mkDict tvarOrder))
  end;


fun reg_alloc def =
  let
    val (fname, fbody) = dest_eq (concl def)
    val (args,body) = dest_pabs fbody
    val regenv = args_env args
    val args1 = assgn_args args regenv
    val dest = Term `r0:num`
    val cont = dest
    val body1 = #1 (g_repeat dest cont regenv body)
    val body2 = alloc_mem body1

    val th1 = GSYM (PBETA_RULE (SIMP_CONV pure_ss [LET_SAVE, LET_LOC] body2))
            handle HOL_ERR _ => REFL body2
    val body3 = lhs (concl (th1))
    val th2 = ALPHA fbody (mk_pabs (args1,body3))
    val th3 = CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [th1])) th2
    val th4 = TRANS def th3
    val th5 = (BETA_RULE o REWRITE_RULE [save_def, loc_def]) th4
  in
    th5
  end

(* --------------------------------------------------------------------*)

end