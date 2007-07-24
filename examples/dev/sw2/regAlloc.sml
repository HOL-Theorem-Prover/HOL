structure regAlloc  :> regAlloc  =
struct

(* app load ["NormalTheory", "Normal", "basic"] *)

open HolKernel Parse boolLib bossLib;
open pairLib pairSyntax PairRules NormalTheory Normal basic;

(* --------------------------------------------------------------------*)
(* --------------------------------------------------------------------*)

structure M = Binarymap
structure S = Binaryset
val VarType = ref (Type `:word32`) (* numSyntax.num *)

(* --------------------------------------------------------------------*)
(* Datatypes                                                           *)
(* --------------------------------------------------------------------*)

datatype alloc_result =
    Alloc of term (* allocated register *)
  | Spill of term (* spilled variable *)

(* --------------------------------------------------------------------*)
(* Configurable setting                                                *)
(* The "DEBUG" controls whether debugging information should be print  *)
(*    out or not.                                                      *)
(* The "numRegs" stores how many registers are available.              *)
(* By default the register set contains {r0,r1,...}                    *)
(* Users can customize this set by specifying the "regL" or modify the *)
(*   "mk_regs()" function.                                             *) 
(* --------------------------------------------------------------------*)

val DEBUG = ref true;

val numRegs = ref 10;

fun mk_regs() = 
  let 
    fun f n = if n = !numRegs then [] else mk_var("r" ^ Int.toString(n) , !VarType) :: f(n+1)
  in
    f 0
  end

val regL = ref (mk_regs());

(* --------------------------------------------------------------------*)
(* Pre-defined variables and functions                                 *)
(* --------------------------------------------------------------------*)

fun is_reg x = (String.sub (term_to_string x,0) = #"r")
fun is_mem x = (String.sub (term_to_string x,0) = #"m")

fun tvarOrder (t1:term,t2:term) =
  let val (s1,s2) = (term_to_string t1, term_to_string t2) in
    if s1 > s2 then GREATER
    else if s1 = s2 then EQUAL
    else LESS
  end;

(* Is an expression a function application? *)
 
fun is_fun exp = 
  (* is_var exp andalso *) 
  (#1 (dest_type (type_of exp)) = "fun")
  handle _ => false;

(* --------------------------------------------------------------------*)
(* make variables                                                      *)
(* mvar -- memory variables                                            *)
(* tvar -- tempory variables; used for spilling.                       *)
(* --------------------------------------------------------------------*)

fun num2name stem i = stem ^ Lib.int_to_string i
val mStrm = ref (Lib.mk_istream (fn x => x+1) 0 (num2name "m"))
val tStrm = ref (Lib.mk_istream (fn x => x+1) 0 (num2name "t"))

fun reset_mvar () = mStrm := Lib.mk_istream (fn x => x+1) 0 (num2name "m")
fun next_mvar () = mk_var (state(next (!mStrm)), !VarType)
fun cur_mvar() = state(!mStrm)
fun reset_tvar () = tStrm := Lib.mk_istream (fn x => x+1) 0 (num2name "t")
fun next_tvar () = mk_var (state(next (!tStrm)), !VarType)

(* --------------------------------------------------------------------*)
(* The variables that have not been allocated                          *)
(* --------------------------------------------------------------------*)

fun fv exp = 
  let val xs = free_vars exp
      val xs' = List.filter (fn x => not (is_mem x orelse is_reg x)) xs
  in  xs'
  end

(* --------------------------------------------------------------------*)
(* Attempt to allocate a register                                      *)
(* "regenv" -- the current allocation scheme;                          *)
(* "cont" -- the continuation that contains live variables;            *)
(* "x" -- the variable to be allocated.                                *)
(* --------------------------------------------------------------------*)

(* allocate a register or spill a variable *)

fun alloc_one cont regenv x =
  let val all = !regL (* allregs *) in
    if is_reg x then Alloc(x) else
    let 
      val free = fv cont
      val live =    (* the set of registers already assigned to the live variables in cont *)
        List.foldl
          (fn (y,live) =>
            if is_reg y then S.add (live,y) else       (* registers that have been used *)
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
(* For Tuple and Function calls                                        *)
(* Rules for replacing variables with registers or memory slots.       *)
(* --------------------------------------------------------------------*)

fun find_pos (regenv,x) =
  if is_reg x orelse is_word_literal x orelse numSyntax.is_numeral x orelse is_const x then x
  else
    let val v = M.find (regenv, x) in
      if is_reg v orelse is_mem v then v
      else raise (Fail "find_pos...")
    end 
  ;

fun tuple_subst_rules xs regenv =
    List.foldl
      (fn (x,ys) =>
        if is_var x then (x |-> find_pos (regenv, x)) :: ys
        else ys)
      []
      xs;

(* --------------------------------------------------------------------*)
(* Attempt to allocate registers for a tuple                           *)
(* If the tuple contains only one variable, we always allocate a       *)
(* register for it by spilling another variable;                       *)
(* on the other hand, if the tuple contains several variables, and some*)
(* of them couldn't be assigned registers, we always spill them into   *)
(* the memory. (this can be optimized a little)                        *)
(* --------------------------------------------------------------------*)

fun alloc cont regenv x =
  if is_pair x then
    let 
      val xs = strip_pair x
      val env =
        #2(List.foldl 
          (fn (t, (cont', env')) => 
	     case alloc_one cont' env' t of 
	        Alloc(r) => (mk_pair(cont', t), M.insert(env', t, r))           (* assign a register *) 
              | Spill(n) => (mk_pair(cont',t), M.insert(env', t, next_mvar()))  (* assign a memory slot *)
	  ) (cont,regenv) xs
        ) 
    in
     (Alloc(subst (tuple_subst_rules xs env) x), env)
    end
  else            (* single variable *)
     case alloc_one cont regenv x of 
	 Alloc(r) => (Alloc(r), M.insert(regenv, x, r))
      |  Spill(n) => (Spill(n), regenv)
  ;

(* --------------------------------------------------------------------*)
(* Register Allocation                                                 *)
(* Auxiliary data structures and functions                             *)
(* --------------------------------------------------------------------*)

datatype AllocResult =
    NoSpill of term * (term, term) M.dict (* new regenv *)
  | ToSpill of term * term list           (* spilled variables *)

exception regAlloc of string
exception NoReg of term

fun find_reg (regenv,x) =
  if is_reg x then x
  else if is_word_literal x orelse numSyntax.is_numeral x orelse is_const x then x
  else
    let val v = M.find (regenv, x) in
      if is_reg v then v
      else raise (NoReg x)
    end
  handle NotFound => raise (NoReg x)

fun mk_subst_rules xs regenv =         (* replace variables with registers *)
    List.foldl
      (fn (x,ys) =>
        if is_var x then (x |-> find_reg (regenv, x)) :: ys
        else ys)
      []
      xs;

(* let x = (let v = M in N) in e2   --> let x = M in let v = N in e2 *)

fun concat e1 x e2 = 
  if is_let e1 then 
    let val (v,M,N) = dest_plet e1 in
        mk_plet (v, M, concat N x e2)
    end
  else 
    mk_plet (x, e1, e2)

(* Add a mapping into the environment *)

fun add x r regenv =
  if is_reg x then regenv
  else M.insert(regenv, x, r)

fun list_mem x xs =  (*  membership in a list   *)
  not ((List.find (fn k => (k = x)) xs) = NONE)

(* --------------------------------------------------------------------*)
(* Spill to memory                                                     *)
(* Restore from memory                                                  *)
(* --------------------------------------------------------------------*)

fun save x exp regenv =
  let val v = next_mvar()
      val regenv1 = M.insert(regenv, x, v)    (* x is spilled to memory *)
      val _ = if !DEBUG then 
                print ("saving " ^ term_to_string x ^ " to " ^ term_to_string v ^"\n")
               else ()
  in 
     (mk_plet (v, M.find(regenv,x), exp), regenv1)   (* let m[.] = r[.] in exp[m[.]] *)
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

(* g' is for allocating registers in expressions *)

fun g' dest cont regenv exp =
  if is_word_literal exp orelse numSyntax.is_numeral exp orelse is_const exp orelse 
     is_fun exp orelse is_mem exp then NoSpill (exp, regenv)
  else if is_var exp then NoSpill (subst (mk_subst_rules [exp] regenv) exp, regenv)
  else if is_cond exp then
    let val (c,e1,e2) = dest_cond exp
        val (cmpop,ds) = strip_comb c
        val (d0,d1) = (hd ds, hd (tl ds))
        (*
        val (ds0,ds1) = (#2 (strip_comb d0), #2 (strip_comb d1))
        val c' = list_mk_comb (cmpop, [subst (mk_subst_rules ds0 regenv) d0, subst (mk_subst_rules ds1 regenv) d1])
        *)
        val c' = list_mk_comb (cmpop, [find_reg(regenv,d0), find_reg(regenv,d1)])
        fun f e1 e2 = mk_cond(c', e1, e2)
    in
        g'_if dest cont regenv exp f e1 e2
    end
  else if is_pair exp then
      NoSpill (subst (tuple_subst_rules (strip_pair exp) regenv) exp, regenv)
  else if is_let exp then
       g dest cont regenv exp
  else if is_comb exp then
    let val (op0,xs) = strip_comb exp in
      if is_binop op0 (* includes orelse is_cmpop op0 orelse is_relop op0 *)
      then
        NoSpill (subst (mk_subst_rules xs regenv) exp, regenv)
      else if is_fun op0 then  (* function application *)
        let val ys = List.foldl (fn (t, ls) => (strip_pair t) @ ls) [] xs
        in  NoSpill (subst (tuple_subst_rules ys regenv) exp, regenv)
        end
      else raise regAlloc
          ("g': this case hasn't been unimplemented -- " ^ term_to_string exp)
    end
  else NoSpill (exp, regenv)

and

(* when g' accesses a spilled variable, a NoReg exception is raised since we cannot find the variable in regenv. 
   Thus a restore is required, which restores the value of a variable from the memory to a register. *)

g'_and_restore dest cont regenv exp =
  g' dest cont regenv exp
  handle NoReg x =>                              (* x is stored in the memory, need to be assigned a register *)
      g dest cont regenv (restore x exp regenv)  (* restore the spilled x from the memory *)

and

(* g deals with the let v = ... in ... structure.  *)

 g dest cont regenv exp = 
  if is_let exp then                        (*  exp = LET (\v. N) M  *)
     let
       val (x,M,N) = dest_plet exp
       val cont' = mk_pair(N, cont) (* concat N dest cont *)
     in
       if is_mem x orelse is_reg x then 
          case (g x cont regenv N) of
               ToSpill(e2, ys) =>
                 ToSpill (exp, ys)
            |  NoSpill(e2, regenv2) => NoSpill(mk_plet(x,M,e2), regenv2)
       else
       case g'_and_restore x cont' regenv M of
            ToSpill(exp1, ys) => ToSpill(concat exp1 x N, ys)
         |  NoSpill(exp1, regenv1) =>
            ( case (alloc cont' regenv1 x) of
                 (Spill(y), env) => 
                     let val op_vars = free_vars N
                     in
		       (if list_mem y op_vars then
                         ToSpill (exp, [#1 (valOf(List.find (fn (key,value) =>
                                          is_reg value andalso not (list_mem key op_vars)) (M.listItems(env))))])
                       else ToSpill (exp, [y]))
                       handle _ => ToSpill (exp, [y])
(*
		       (if list_mem y op_vars then
			 ToSpill (exp, [valOf(List.find (fn t => 
					  is_reg (M.find(regenv1,t)) andalso not (list_mem t op_vars)
					  handle _ => false) (free_vars cont'))])
		       else ToSpill (exp, [y]))
                       handle _ => ToSpill (exp, [y])
*)
                     end
              |  (Alloc(r), env) => 
		     let val (exp2,env') = g_repeat dest cont env N
                     in NoSpill(concat exp1 r exp2, env')
                     end
(*
		   (case (g dest cont env N) of
                     ToSpill(e2, ys) =>
                       if list_mem x ys then
                          let val (e',regenv') = save x e2 (add x r regenv1) cont
                              val x_saved = concat exp1 r e' in
                            (case List.filter (fn y => y <> x) ys of
                                  []      => g dest cont regenv' x_saved
                               |  ys_left => ToSpill(x_saved, ys_left)
                            )
                          end
                       else
                         ToSpill (mk_plet(x,M,N), ys)
                      |  NoSpill(e2', regenv2) => NoSpill(concat exp1 r e2', regenv2)
                   )
*)
            )
     end
  else
     g'_and_restore dest cont regenv exp
 
and

g_repeat dest cont regenv exp =                  (*  early spilling *)
   case g dest cont regenv exp of
      NoSpill(exp', regenv') => (exp', regenv')
    | ToSpill(exp, xs) =>
        let val (exp,regenv) = 
              List.foldl
               (fn (x,(exp,env)) => save x exp env)
               (exp, regenv)
               xs
        in
          g_repeat dest cont regenv exp
        end

and

g'_if dest cont regenv exp constr e1 e2 = 
  let 
    val (e1', regenv1) = g_repeat dest cont regenv e1
    val (e2', regenv2) = g_repeat dest cont regenv e2
    val regenv' = List.foldl (fn ((key,value), m) => M.insert(m,key,value)) regenv1 (M.listItems regenv2)
  in
    NoSpill(constr e1' e2', regenv')
  end

(* The following code is needed only for non-SSA expressions 
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
*)

(* --------------------------------------------------------------------*)
(* Reduce the number of memory slots by reusing memory variables.      *)
(* The mechanism is similar to that of allocating registers; but we    *)
(* unlimited number of memory slots.                                   *)
(* --------------------------------------------------------------------*)

(* The first available memory slot that doesn't conflict with live "slots" *)

fun first_avail_slot env cont = 
  let 
      fun indexOfSlot s = valOf(Int.fromString(String.substring(s, 1, String.size s - 1)))

      val live = List.foldl (fn (t,ts) => 
			     let val x = M.find(env,t) in 
				 if is_mem x then x ::ts else ts end handle _ => ts) [] (free_vars cont)
      val max_slot = indexOfSlot(state(!mStrm))
      fun candidate i =  (* the first available register *)
        if i > max_slot then next_mvar()
        else
          let val cur_slot = mk_var("m" ^ Int.toString i, !VarType)
          in if list_mem cur_slot live then
	        candidate (i+1)
             else cur_slot
          end
  in
     candidate 1
  end

(* reuse memory slots that will be "live" any more *)

fun alloc_mem (args,body) =
  let
     val body' = rhs (concl (SIMP_CONV bool_ss [ELIM_USELESS_LET] body)) handle _ => body
     val (save,loc) = (mk_const("save", mk_type("fun",[!VarType, !VarType])),
		       mk_const("loc", mk_type("fun",[!VarType, !VarType])))

     fun trav t env cont =
       if is_let t then
           let val (v,M,N) = dest_plet t
           in 
              if is_mem v then
                let val v' = first_avail_slot env (mk_pair(N,cont))
                    val M' = mk_comb (save, M)
                    val env' = M.insert (env, v, v')
                    val N' = trav N env' cont
                in
                    mk_plet (v', M', N')
                end
              else if is_var M andalso is_mem M then
                let val M' = mk_comb (loc, M.find (env, M))
                    val N' = trav N env cont
                in
                    mk_plet (v, M', N')
                end
              else if is_pair v then 
		let val cont' = mk_pair(N,cont)
		    val (v',env') = 
		        List.foldl (fn (x, (w, env')) => 
		          if not (is_mem x) then (w,env')
		          else 
                            let val x' = first_avail_slot env' cont'
                            in (subst [x |-> x'] w, M.insert(env', x, x'))
                            end) (v,env) (strip_pair v)
                in
                    mk_plet (v', trav M env' cont', trav N env' cont)
                end
              else mk_plet (v, trav M env cont, trav N env cont)
            end
       else if is_comb t then
            let val (M1,M2) = dest_comb t
                val M1' = trav M1 env cont
                val M2' = trav M2 env cont
            in mk_comb(M1',M2')
            end
       else if is_mem t then
           mk_comb (loc, M.find (env, t) handle _ => t)
       else t

     val memenv = List.foldl (fn (t, m) => if is_mem t then (next_mvar(); M.insert(m,t,t)) else m) (M.mkDict tvarOrder) (strip_pair args)
     fun move_mindex i = if i = M.numItems memenv then () else (next_mvar();move_mindex (i + 1))

  in
     (reset_mvar ();
      move_mindex 0;
      trav body' memenv ``()``
     )
  end;

(* --------------------------------------------------------------------*)
(* Register Allocation                                                 *)
(* --------------------------------------------------------------------*)

fun reset () = 
  (regL := mk_regs();
   reset_mvar();
   reset_tvar()
  )

(* Assign registers to inputs; memory slots will be used when there are too many paramenters *)

fun args_env args = 
   let val argL = strip_pair args
       fun assgn_v (v,(i,regenv)) = 
            (i+1, M.insert (regenv, v, 
		if i < !numRegs then mk_var ("r" ^ Int.toString i, !VarType)
                else next_mvar()))
   in
       #2 (List.foldl assgn_v (0, M.mkDict tvarOrder) argL)
   end

(* step1: configurate the environment;
   step2: obtain a allocation scheme by term rewriting;
   step3: prove the correctness of the scheme by showing the result is alpha-equivalent to the source program
*)

fun reg_alloc def =
  let
    val (fname, fbody) = dest_eq (concl def)
    val (args,body) = dest_pabs fbody
    val (sane,var_type) = pre_check(args,body)
  in
    if sane then
      let
    	val _ = (VarType := var_type; reset())        (* set the variable type according to the given program *)
    	val regenv = args_env args
    	val args1 = subst (tuple_subst_rules (strip_pair args) regenv) args
    	val dest = hd (!regL); (* assgn_exp (last_exp body) *)
    	val cont = dest
    	val body1 = #1 (g_repeat dest cont regenv body)
    	val body2 = alloc_mem(args1,body1)

    	val th1 = GSYM (PBETA_RULE (SIMP_CONV pure_ss [LET_SAVE, LET_LOC, loc_def] body2))
            handle _ => REFL body2
    	val body3 = lhs (concl (th1))
    	val th2 = ALPHA fbody (mk_pabs (args1,body3))
		  handle e => (print "the allocation is incomplete or incorrect"; Raise e)
    	val th3 = CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [th1])) th2
    	val th4 = TRANS def th3
    	val th5 = (BETA_RULE o REWRITE_RULE [save_def, loc_def]) th4
      in
    	th5
      end
    else
     ( print("The source program is invalid! (e.g. all variables are not of the same type)");
       def
     )
  end

(* --------------------------------------------------------------------*)

end
