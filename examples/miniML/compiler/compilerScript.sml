open HolKernel bossLib boolLib pairLib listTheory bytecodeTheory lcsymtacs
open MiniMLTheory compileProofsTheory

val _ = new_theory "compiler"

(* values in compile-time environment *)
(* CTStack n means stack[frame_size - n]
   CTEnv n means El n of the environment (which should be at stack[frame_size])
   CTCode n means El n of the environment, but it's a code pointer,
   so needs to be wrapped up as a closure (using the same environment) *)
val _ = Hol_datatype`
  ctbind = CTStack of num | CTEnv of num | CTCode of num`

val _ = Hol_datatype`
  compiler_state =
  <|
    env: (varN,ctbind) env
  ; next_label: num
  ; inst_length: bc_inst -> num
  |>`

val compile_lit_def = Define`
  (compile_lit (IntLit  n) = PushInt n)
∧ (compile_lit (Bool b) = PushInt (bool2num b))`;

val compile_val_def = tDefine "compile_val"`
  (compile_val (Lit l) = [Stack (compile_lit l)])
∧ (compile_val (Conv NONE ((Lit (IntLit c))::vs)) =
   let n  = LENGTH vs in
   if n = 0 then [Stack (PushInt c)] else
   let vs = FLAT (MAP compile_val vs) in
   SNOC (Stack (Cons (Num c) n)) vs)
(* literals and desugared constructors only *)`
(WF_REL_TAC `measure v_size` >>
 Induct >>
 srw_tac [][] >>
 fsrw_tac [ARITH_ss][exp_size_def,LENGTH_NIL] >>
 res_tac >> Cases_on `vs=[]` >> fsrw_tac [][] >>
 DECIDE_TAC)

val compile_opn_def = Define`
  (compile_opn Plus   = [Stack Add])
∧ (compile_opn Minus  = [Stack Sub])
∧ (compile_opn Times  = [Stack Mult])
∧ (compile_opn Divide = []) (* TODO *)
∧ (compile_opn Modulo = []) (* TODO *)`

val offset_def = Define`
  offset len xs = SUM (MAP len xs) + LENGTH xs`

val emit_def = Define`
  emit s ac is = (ac++is, s with next_label := s.next_label + offset s.inst_length is)`;

val compile_varref_def = tDefine "compile_varref" `
  (compile_varref z ls (CTStack n) = Stack (Load (z - n)) :: ls)
∧ (compile_varref z ls (CTEnv n) = Stack (Load z) :: Stack (El n) :: ls)
∧ (compile_varref z ls (CTCode n) =
   compile_varref z (Stack (Load z) :: Stack (Cons 0 2) :: ls) (CTEnv n))`
(WF_REL_TAC `measure (λ(a,b,x). case x of CTEnv x => 0 | CTCode x => 1)`)

(* compile : exp * compiler_state → bc_inst list * compiler_state *)
val compile_def = tDefine "compile" `
  (compile (Raise err, s) = ARB) (* TODO *)
∧ (compile (Val v, s) = emit s [] (compile_val v))
∧ (compile (Mat e pes, s) = ARB) (* Disallowed: use remove_mat *)
∧ (compile (Con NONE [(Val (Lit (IntLit i)))], s) =
   emit s [] [Stack (PushInt i)])
∧ (compile (Con NONE ((Val (Lit (IntLit i)))::es), s) =
   let n = LENGTH es in
   let (es,s) = FOLDR (λe (es,s). let (e,s) = compile (e,s) in (es++e,s)) ([],s) es in
   let (r,s) = emit s es [Stack (Cons (Num i) n)] in
   (r,s))
∧ (compile (Con _ _, s) = ARB) (* Disallowed: use remove_ctors *)
∧ (compile (Proj e n, s) =
   let (e,s) = compile (e,s) in
   let (r,s) = emit s e [Stack (El n)] in
   (r,s))
∧ (compile (Let x e b, s) =
   let (e,s) = compile (e,s) in
   let (r,s) = compile_bindings s.env b (LENGTH s.env - 0) s [x] in
     (e++r,s)) (* TODO: avoid calls to LENGTH? *)
∧ (compile (Var x, s) =
   case lookup x s.env of
     NONE => ARB (* should not happen *)
   | SOME ct => emit s [] (compile_varref (LENGTH s.env) [] ct))
∧ (compile (App Opapp e1 e2, s) =
  (* A closure looks like:
       Block 0 [CodePtr ck; Block 0 [CodePtr c1; ...; CodePtr cn; v1; ...; vm]]
       where
         v1,...,vm = values of free variables (the environment)
         c1,...,cn = code of all functions sharing the environment
         ck = this function's code (thus ck appears twice)
       Non-recursive closures omit the initial list of CodePtrs *)
   let (e1,s) = compile (e1,s) in
   let (e2,s) = compile (e2,s) in
   (* stack = arg :: Block 0 [CodePtr ck; env] :: rest *)
   let (r,s) = emit s (e1++e2) [Stack (Load 1); Stack (El 0)] in
   (* stack = CodePtr ck :: arg :: Block 0 [CodePtr ck; env] :: rest *)
   let (r,s) = emit s r [Stack (Load 2); Stack (El 1); Stack (Store 2)] in
   (* stack = CodePtr ck :: arg :: env :: rest *)
   let (r,s) = emit s r [CallPtr] in
   (* stack = arg :: CodePtr ret :: env :: rest *)
     (r,s))
∧ (compile (Letrec defs b, s) = (* TODO: more efficient than LENGTH and MAP? *)
   let (r1,s) = compile_closures (SOME (MAP FST defs)) s (MAP SND defs) in
   let (r2,s) = compile_bindings s.env b (LENGTH s.env + 1 - LENGTH defs) s (MAP FST defs) in
     (r1++r2,s))
∧ (compile (Fun x b, s) = compile_closures NONE s [(x,b)])
∧ (compile (App Equality e1 e2, s) =
   let (e1,s) = compile (e1,s) in
   let (e2,s) = compile (e2,s) in
   emit s (e1++e2) [Stack Equal])
∧ (compile (App (Opn op) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    emit s (e1++e2) (compile_opn op))
∧ (compile (App (Opb Lt) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    emit s (e1++e2) [Stack Less])
∧ (compile (App (Opb Geq) e1 e2, s)
  = let (e2,s) = compile (e2,s) in
    let (e1,s) = compile (e1,s) in
    emit s (e2++e1) [Stack Less])
∧ (compile (App (Opb Gt) e1 e2, s)
  = let (e0,s) = emit s [] [Stack (PushInt 0)] in
    let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    emit s (e0++e1++e2) [Stack Sub;Stack Less])
∧ (compile (App (Opb Leq) e1 e2, s)
  = let (e0,s) = emit s [] [Stack (PushInt 0)] in
    let (e2,s) = compile (e2,s) in
    let (e1,s) = compile (e1,s) in
    emit s (e0++e2++e1) [Stack Sub;Stack Less])
∧ (compile (Log And e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (aa,s) = emit s ARB [JumpNil ARB] in
    let (e2,s) = compile (e2,s) in
    (e1++[JumpNil s.next_label]++e2, s))
∧ (compile (Log Or e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let f n1 n2 = [JumpNil n1;Stack (PushInt (bool2num T));Jump n2] in
    let (aa,s) = emit s ARB (f ARB ARB) in
    let n1     = s.next_label in
    let (e2,s) = compile (e2,s) in
    let n2     = s.next_label in
    (e1++(f n1 n2)++e2, s))
∧ (compile (If e1 e2 e3, s)
  = let (e1,s) = compile (e1,s) in
    let f n1 n2 = [JumpNil n1;Jump n2] in
    let (aa,s) = emit s ARB (f ARB ARB) in
    let n1     = s.next_label in
    let (e2,s) = compile (e2,s) in
    let (aa,s) = emit s ARB [Jump ARB] in
    let n2     = s.next_label in
    let (e3,s) = compile (e3,s) in
    let n3     = s.next_label in
    (e1++(f n1 n2)++e2++[Jump n3]++e3, s))
∧ (compile_bindings env0 b m s [] =
   let (b,s) = compile (b,s) in
   let (r,s) = emit s b [Stack (Store 0);Stack (Pops (m - (LENGTH env0)))] in
     (r, s with env := env0))
∧ (compile_bindings env0 b m s (x::xs) =
     compile_bindings env0 b
       (m + 1)
       (s with env := bind x (CTStack m) s.env)
       xs)
∧ (compile_closures names s xbs =
   (*  PushInt 0                            0, rest
       Call L1                              0, CodePtr f1, rest
       ?
       ...      (* function 1 body *)
       Store 0  (* replace argument with
                   return value *)
       Return
   L1: Call L2                              0, CodePtr f2, CodePtr f1, rest
       ?
       ...      (* function 2 body *)
       Store 0
       Return
   L2: Call L3
       ?
       ...      (* more function bodies *)
   ...
       Return
   LK: Call L
       ...
       Return   (* end of last function *)
   L:  Pop                                  CodePtr fk, ..., CodePtr f1, rest
       Load ?   (* copy free vars *)
       ...                                  vn, ..., v1, CodePtr fk, ..., CodePtr f1, rest
       (* for non-recursive (nb: k = 1): *)
       Cons 0 n                             Block 0 Env, CodePtr f1, rest
       Cons 0 2                             Block 0 [CodePtr f1; Block 0 Env], rest
       (* for recursive: *)
       Cons 0 (k+n)  Block 0 Env, rest
       Load 0        Block 0 Env, Block 0 Env, rest
       El 1          CodePtr f2, Block 0 Env, rest
       Load 1        Block 0 Env, CodePtr f2, Block 0 Env, rest
       Cons 0 2      f2, Block 0 Env, rest
       Load 1        Block 0 Env, f1, Block 0 Env, rest
       El 2          CodePtr f3, f1, Block 0 Env, rest
       Load 2        Block 0 Env, CodePtr f3, f1, Block 0 Env, rest
       Cons 0 2      f3, f2, Block 0 Env, rest
       ...
       Cons 0 2      fk, ..., f2, Block 0 Env, rest
       Load (k-2+1)  Block 0 Env, fk, ..., f2, Block 0 Env, rest
       El 0          CodePtr f1, fk, ..., f2, Block 0 Env, rest
       Load k        Block 0 Env, CodePtr f1, fk, ..., f2, Block 0 Env, rest
       Cons 0 2      f1, fk, ..., f2, Block 0 Env, rest
       Store k       fk, ..., f1, rest
  *)
   let fvs = FOLDL (λfvs (x,b). free_vars (Fun x b)) {} xbs in
   let fvs = case names of NONE => fvs | SOME names => fvs DIFF (set names) in
   let z = LENGTH s.env in
   let (e,i,ldenv) =
     FOLDL (λ(e,i,ls) (v,n).
             if v IN fvs
             then (bind v (CTEnv i) e, i + 1, compile_varref z ls n)
             else (e,i,ls))
      ([],0,[]) s.env in
   let (e,j) = case names of NONE => (e,0)
     | SOME names => FOLDR (λn (e,j). (bind n (CTCode j) e, j + 1)) (e,0) names
     in
     (* first "" is the environment, second is return ptr *)
   let e = bind "" (CTStack 1) (bind "" (CTStack 0) e) in
   let (r,s) = emit s [] [Stack (PushInt 0)] in
   let (r,s,ls) = FOLDR (λ(x,b) (r,s,ls).
                       let i = LENGTH r in
                       let (r,s) = emit s r [Call ARB] in
                       let s' = s with env := bind x (CTStack 2) e in
                       let (b,s') = compile (b,s') in
                       let s = s' with env := s.env in
                       let (r,s) = emit s (r++b) [Stack (Store 0);Return] in
                         (r,s,(i,s.next_label)::ls))
                   (r,s,[])
                   xbs in
   let r = FOLDR (λ(i,n) r. REPLACE_ELEMENT (Call n) i r) r ls in
   let (r,s) = emit s r (Stack Pop :: ldenv) in
   case names of NONE => emit s r [Stack (Cons 0 i); Stack (Cons 0 2)]
   | SOME names =>
   let (r,s) = emit s r [Stack (Cons 0 (i+j))] in
   let (r,s,n) = FOLDR (λa (r,s,n).
     let (r,s) = emit s r [Stack (Load n);
                           Stack (El (n+1));
                           Stack (Load (n+1));
                           Stack (Cons 0 2)]
     in (r,s,n+1)) (r,s,0) (TL names) in
   let k = LENGTH (TL names) in
   emit s r [Stack (Load k);
             Stack (El 0);
             Stack (Load (k+1));
             Stack (Cons 0 2);
             Stack (Store (k+1))])`
( WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       | INL (e,s) => (exp_size e, 3:num)
       | INR (INL (env,e,n,s,[])) => (exp_size e, 4)
       | INR (INL (env,e,n,s,ns)) =>
         (exp_size e +
          SUM (MAP (list_size char_size) ns) + LENGTH ns, 2)
       | INR (INR (NONE,s,xbs)) => (SUM (MAP exp4_size xbs), 1)
       | INR (INR (SOME ns,s,xbs)) =>
         (SUM (MAP exp4_size xbs) +
          SUM (MAP (list_size char_size) ns) + LENGTH ns, 0))` >>
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][exp8_size_thm,exp1_size_thm,SUM_MAP_exp2_size_thm,exp_size_def] >- (
    Q.ISPEC_THEN `exp_size` imp_res_tac SUM_MAP_MEM_bound >>
    DECIDE_TAC )
  >- (
    Q.ISPEC_THEN `exp4_size` imp_res_tac SUM_MAP_MEM_bound >>
    Cases_on `names` >> rw[] >>
    fs[exp_size_def] >>
    DECIDE_TAC ) >>
  TRY (Cases_on `defs`) >>
  TRY (Cases_on `xs`) >>
  srw_tac[ARITH_ss][])

val _ = export_theory ()
