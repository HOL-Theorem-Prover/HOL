open HolKernel bossLib boolLib pairLib listTheory bytecodeTheory lcsymtacs
open MiniMLTheory compileProofsTheory

val _ = new_theory "compiler"

(* values in compile-time environment *)
(* CTStack n means stack[sz - n]
   CTEnv n means El n of the environment (which should be at stack[sz])
   CTCode n means El n of the environment, but it's a code pointer,
   so needs to be wrapped up as a closure (using the same environment) *)
val _ = Hol_datatype`
  ctbind = CTStack of num | CTEnv of num | CTCode of num`

val _ = Hol_datatype`
  compiler_state =
  <|
    env: (varN,ctbind) env
  ; sz: num
  ; next_label: num
  ; inst_length: bc_inst -> num
  |>`

val compile_lit_def = Define`
  (compile_lit (IntLit  n) = PushInt n)
∧ (compile_lit (Bool b) = PushInt (bool2num b))`;

val compile_val_def = Define `
  (compile_val (Lit l) = [Stack (compile_lit l)]) ∧
  (compile_val _ = [Jump 1006])` (* Disallowed *)

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
  (compile_varref sz ls (CTStack n) = Stack (Load (sz - n)) :: ls)
∧ (compile_varref sz ls (CTEnv n) = Stack (Load sz) :: Stack (El n) :: ls)
∧ (compile_varref sz ls (CTCode n) =
   compile_varref sz (Stack (Load sz) :: Stack (Cons 0 2) :: ls) (CTEnv n))`
(WF_REL_TAC `measure (λ(a,b,x). case x of CTEnv x => 0 | CTCode x => 1)`)

(* compile : exp * compiler_state → bc_inst list * compiler_state *)
val compile_def = tDefine "compile" `
  (compile (Raise err, s) = emit s [] [Jump 1000]) (* TODO *)
∧ (compile (Val v, s) =
   let (r,s) = emit s [] (compile_val v) in
     (r, s with sz := s.sz + 1))
∧ (compile (Mat e pes, s) = emit s [] [Jump 1001]) (* Disallowed: use remove_mat *)
∧ (compile (Con NONE [(Val (Lit (IntLit i)))], s) =
   let (r,s) = emit s [] [Stack (PushInt i)] in
     (r, s with sz := s.sz + 1))
∧ (compile (Con NONE ((Val (Lit (IntLit i)))::es), s) =
   let n = LENGTH es in
   let (es,s) = FOLDL (λ(es,s) e. let (e,s) = compile (e,s) in (es++e,s)) ([],s) es in
   let (r,s) = emit s es [Stack (Cons (Num i) n)] in
   (r,s with sz := s.sz + 1 - n))
∧ (compile (Con _ _, s) = emit s [] [Jump 1002]) (* Disallowed: use remove_ctors *)
∧ (compile (Proj e n, s) =
   let (e,s) = compile (e,s) in
   case n of 0 =>
   let (r,s) = emit s [] [Stack (Load 0); Stack IsNum; JumpNil ARB;
                          Stack Tag; Stack (Pops 1)] in
   let r = REPLACE_ELEMENT (JumpNil s.next_label) 2 r in
     (e++r,s)
   | SUC n => emit s e [Stack (El n)])
∧ (compile (Let x e b, s) =
   let (e,s) = compile (e,s) in
   let (r,s) = compile_bindings s.env b 0 s [x] in
     (e++r,s)) (* TODO: detect nested Lets? *)
∧ (compile (Var x, s) =
   case lookup x s.env of
     NONE => emit s [] [Jump 1003] (* should not happen *)
   | SOME ct =>
     let (r,s) = emit s [] (compile_varref s.sz [] ct) in
     (r, s with sz := s.sz + 1))
∧ (compile (App Opapp e1 e2, s) =
  (* A closure looks like:
       Block 0 [CodePtr ck; Block 0 [CodePtr c1; ...; CodePtr cn; v1; ...; vm]]
       where
         v1,...,vm = values of free variables (the environment)
         c1,...,cn = code of all functions sharing the environment
         ck = this function's code (thus ck appears twice)
       Non-recursive closures omit the initial list of CodePtrs.
       If they additionally don't have any free variables, the
       entire environment block is replaced by Number 0. *)
   let (e1,s) = compile (e1,s) in
   let (e2,s) = compile (e2,s) in
   (* stack = arg :: Block 0 [CodePtr ck; env] :: rest *)
   let (r,s) = emit s (e1++e2) [Stack (Load 1); Stack (El 0)] in
   (* stack = CodePtr ck :: arg :: Block 0 [CodePtr ck; env] :: rest *)
   let (r,s) = emit s r [Stack (Load 2); Stack (El 1)] in
   (* stack = env :: CodePtr ck :: arg :: Block 0 [CodePtr ck; env] :: rest *)
   let (r,s) = emit s r [Stack (Store 2)] in
   (* stack = CodePtr ck :: arg :: env :: rest *)
   let (r,s) = emit s r [CallPtr] in
   (* before call stack = arg :: CodePtr ret :: env :: rest
      after call stack = retval :: env :: rest *)
   let (r,s) = emit s r [Stack (Pops 1)] in
   (* stack = retval :: rest *)
     (r,s with sz := s.sz - 1))
∧ (compile (Letrec defs b, s) = (* TODO: more efficient than LENGTH and MAP? *)
   let (r1,s) = compile_closures (SOME (MAP FST defs)) s (MAP SND defs) in
   let (r2,s) = compile_bindings s.env b 0 s (MAP FST defs) in
     (r1++r2,s))
∧ (compile (Fun x b, s) = compile_closures NONE s [(x,b)])
∧ (compile (App Equality e1 e2, s) =
   let (e1,s) = compile (e1,s) in
   let (e2,s) = compile (e2,s) in
   let (r,s) = emit s (e1++e2) [Stack Equal] in
     (r, s with sz := s.sz - 1))
∧ (compile (App (Opn op) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    let (r,s) = emit s (e1++e2) (compile_opn op) in
      (r, s with sz := s.sz - 1))
∧ (compile (App (Opb Lt) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    let (r,s) = emit s (e1++e2) [Stack Less] in
      (r, s with sz := s.sz - 1))
∧ (compile (App (Opb Leq) e1 e2, s)
  = let (e0,s) = emit s [] [Stack (PushInt 1); Stack (PushInt 0)] in
    let s = s with sz := s.sz + 2 in
    let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    let (r,s) = emit s (e0++e1++e2) [Stack Sub;Stack Less;Stack Sub] in
      (r, s with sz := s.sz - 3))
∧ (compile (App (Opb Gt) e1 e2, s) = emit s [] [Jump 1004]) (* Disallowed: use remove_Gt_Geq *)
∧ (compile (App (Opb Geq) e1 e2, s) = emit s [] [Jump 1005]) (* Disallowed: use remove_Gt_Geq *)
∧ (compile (Log And e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (aa,s) = emit s ARB [JumpNil ARB] in
    let s = s with sz := s.sz - 1 in
    let (e2,s) = compile (e2,s) in
    (e1++[JumpNil s.next_label]++e2, s))
∧ (compile (Log Or e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let f n1 n2 = [JumpNil n1;Stack (PushInt (bool2num T));Jump n2] in
    let (aa,s) = emit s ARB (f ARB ARB) in
    let n1     = s.next_label in
    let s = s with sz := s.sz - 1 in
    let (e2,s) = compile (e2,s) in
    let n2     = s.next_label in
    (e1++(f n1 n2)++e2, s))
∧ (compile (If e1 e2 e3, s)
  = let (e1,s) = compile (e1,s) in
    let f n1 n2 = [JumpNil n1;Jump n2] in
    let (aa,s) = emit s ARB (f ARB ARB) in
    let n1     = s.next_label in
    let s = s with sz := s.sz - 1 in
    let (e2,s) = compile (e2,s) in
    let (aa,s) = emit s ARB [Jump ARB] in
    let n2     = s.next_label in
    let s = s with sz := s.sz - 1 in
    let (e3,s) = compile (e3,s) in
    let n3     = s.next_label in
    (e1++(f n1 n2)++e2++[Jump n3]++e3, s))
∧ (compile_bindings env0 b n s [] =
   let (b,s) = compile (b,s) in
   let (r,s) = emit s b [Stack (Pops n)] in
     (r, s with <| env := env0 ;
                   sz  := s.sz - n |>))
∧ (compile_bindings env0 b n s (x::xs) =
     compile_bindings env0 b
       (n + 1)
       (s with env := bind x (CTStack (s.sz - n)) s.env)
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
   let k = case names of NONE => 1 | SOME names => LENGTH names in
   let (e,i,ldenv) =
     FOLDL (λ(e,i,ls) (v,n).
             if v IN fvs     (* s.sz + k because of CodePtrs produced by Calls *)
             then (bind v (CTEnv i) e, i + 1, compile_varref (s.sz + k) ls n)
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
                       let s' = s with <|
                         env := bind x (CTStack 2) e ;
                         sz  := 2 |> in
                       let (b,s') = compile (b,s') in
                       let s = s' with <|
                         env := s.env ;
                         sz  := s.sz |> in
                       let (r,s) = emit s (r++b) [Stack (Store 0);Return] in
                         (r,s,(i,s.next_label)::ls))
                   (r,s,[])
                   xbs in
   let r = FOLDR (λ(i,n) r. REPLACE_ELEMENT (Call n) i r) r ls in
   case names of
   | NONE =>
   let (r,s) = if i = 0 then (r,s) else
     let (r,s) = emit s r (Stack Pop :: ldenv) in
     emit s r [Stack (Cons 0 i)] in
   let (r,s) = emit s r [Stack (Cons 0 2)] in
     (r, s with sz := s.sz + 1)
   | SOME names =>
   let (r,s) = emit s r (Stack Pop :: ldenv) in
   let (r,s) = emit s r [Stack (Cons 0 (i+j))] in
   let (r,s,n) = FOLDR (λa (r,s,n).
     let (r,s) = emit s r [Stack (Load n);
                           Stack (El (n+1));
                           Stack (Load (n+1));
                           Stack (Cons 0 2)]
     in (r,s,n+1)) (r,s,0) (TL names) in
   let (r,s) =
   emit s r [Stack (Load (k-1));
             Stack (El 0);
             Stack (Load k);
             Stack (Cons 0 2);
             Stack (Store k)] in
   (r, s with sz := s.sz + k))`
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
