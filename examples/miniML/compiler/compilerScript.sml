open HolKernel bossLib boolLib pairLib listTheory bytecodeTheory lcsymtacs
open MiniMLTheory compileProofsTheory

val _ = new_theory "compiler"

val _ = Hol_datatype`
  compiler_state =
  <|
   (* inl is stack variable
      inr is environment (heap) variables: *)
    env: (varN,num+num) env
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
 (* also want div2 and mod2 in ir, to compile to those when possible *)
∧ (compile_opn Divide = []) (* TODO *)
∧ (compile_opn Modulo = []) (* TODO *)`

val offset_def = Define`
  offset len xs = SUM (MAP len xs) + LENGTH xs`

val emit_def = Define`
  emit s ac is = (ac++is, s with next_label := s.next_label + offset s.inst_length is)`;

(* compile : exp * compiler_state → bc_inst list * compiler_state *)
val compile_defn = Hol_defn "compile"` (* tDefine fails *)
  (compile (Raise err, s) = ARB) (* TODO *)
∧ (compile (Val v, s) = emit s [] (compile_val v))
∧ (compile (Mat e pes, s) = ARB) (* TODO; maybe disallow and use some remove_mat? *)
∧ (compile (Con NONE [(Val (Lit (IntLit i)))], s) =
   emit s [] [Stack (PushInt i)])
∧ (compile (Con NONE ((Val (Lit (IntLit i)))::es), s) =
   let n = LENGTH es in
   let (es,s) = FOLDR (λe (es,s). let (e,s) = compile (e,s) in (es++e,s)) ([],s) es in
   let (r,s) = emit s es [Stack (Cons (Num i) n)] in
   (r,s))
∧ (compile (Con _ _, s) = ARB) (* Disallowed; use remove_ctors *)
∧ (compile (Proj e n, s) =
   let (e,s) = compile (e,s) in
   let (r,s) = emit s e [Stack (El n)] in
   (r,s))
∧ (compile (Let x e b, s) =
   let (e,s) = compile (e,s) in
   let n = LENGTH s.env in
   let s' = s with env := bind x (INL n) s.env in  (* TODO: track size separately? *)
   let (b,s') = compile (b,s') in
   let (r,s') = emit s' (e++b) [Stack (Store 0)] in (* replace value of bound var with value of body *)
   (r, s' with env := s.env))
∧ (compile (Letrec defs b, s) = ARB) (* TODO *)
∧ (compile (Var x, s) =
   case lookup x s.env of
     NONE => ARB (* should not happen *)
   | SOME (INL n) => emit s [] [Stack (Load (LENGTH s.env - n))]
   | SOME (INR n) => emit s [] [Stack (Load (LENGTH s.env)); Stack (El n)])
∧ (compile (Fun x b, s) =
   (*  Load ?                               stack:
       ...      (* set up environment *)
       Cons 0 ?                             Cons 0 Env, rest
       Call L                               Cons 0 Env, CodePtr f, rest
       ?
       ...      (* function body *)
       Store 0  (* replace argument with
                   return value *)
       Return
    L: Cons 0 2 (* create closure *)        Cons 0 [CodePtr f, Cons 0 Env], rest
  *)
   let fvs = free_vars (Fun x b) in
   let z = LENGTH s.env in
   let (e,i,ls) =
     FOLDL (λ(e,i,ls) (v,n).
             if v IN fvs
             then (bind v (INR i) e, i + 1,
                   case n of
                   | INL n => Stack (Load (z - n)) :: ls
                   | INR n => Stack (Load z) :: Stack (El n) :: ls)
             else (e,i,ls))
      ([],0,[]) s.env in
   let (r,s) = emit s [] ls in
   let (r,s) = emit s r [Stack (Cons 0 i) ] in
   let s' = s with env := bind x (INL 2) (bind "" (INL 1) (bind "" (INL 0) e)) in
     (* first "" is the environment, second is return ptr *)
   let (aa,s) = emit s ARB [Call ARB] in
   let (b,s') = compile (b,s') in
   let (b,s') = emit s' b [Stack (Store 0);Return] in
   let s = s' with env := s.env in
   let l = s.next_label in
   let (b,s) = emit s b [Stack (Cons 0 2)] in
     (r++[Call l]++b,s))
∧ (compile (App Opapp e1 e2, s) =
   let (e1,s) = compile (e1,s) in  (* A closure looks like Cons 0 [CodePtr code; Cons 0 Env] *)
   let (e2,s) = compile (e2,s) in
   let (r,s) = emit s (e1++e2) [Stack (Load 1); Stack (El 1)] in (* stack after: env, arg, closure, rest *)
   let (r,s) = emit s r [Stack (Load 2); Stack (El 0)] in (* stack after: codeptr, env, arg, closure, rest *)
   let (r,s) = emit s r [Stack (Load 1); Stack (Store 3); Stack (Pops 1)] in (* stack after: codeptr, arg, env, rest *)
   let (r,s) = emit s r [CallPtr] in (* stack after: arg, return ptr, env, rest *)
     (r,s))
∧ (compile (App Equality e1 e2, s) =
 (* want type info? *)
 (* TODO: currently this is pointer equality, but want structural? *)
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
    (e1++(f n1 n2)++e2++[Jump n3]++e3, s))`

val (compile_def,compile_ind) = Defn.tprove (compile_defn,
  WF_REL_TAC `measure (exp_size o FST)` >>
  srw_tac[ARITH_ss][exp8_size_thm] >>
  Q.ISPEC_THEN `exp_size` imp_res_tac SUM_MAP_MEM_bound >>
  DECIDE_TAC)

val _ = export_theory ()
