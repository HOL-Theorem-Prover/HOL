open HolKernel bossLib MiniMLTheory listTheory bytecodeTheory lcsymtacs

val _ = new_theory "compiler"

val _ = Hol_datatype`
  compiler_state =
  <|
    env: (varN,num) env
  ; next_label: num
  ; inst_length: bc_inst -> num
  |>`

val compile_lit_def = Define`
  (compile_lit (Num  n) = PushNum n)
∧ (compile_lit (Bool b) = PushNum (bool2num b))`;

val compile_val_def = tDefine "compile_val"`
  (compile_val (Lit l) = [Stack (compile_lit l)])
∧ (compile_val (Conv NONE ((Lit (Num c))::vs)) =
   let n  = LENGTH vs in
   if n = 0 then [Stack (PushNum c)] else
   let vs = FLAT (MAP compile_val vs) in
   SNOC (Stack (Cons c n)) vs)
(* literals and desugared constructors only *)`
(WF_REL_TAC `measure v_size` >>
 gen_tac >>
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
val compile_def = Define`
  (compile (Raise err, s) = ARB) (* TODO *)
∧ (compile (Val v, s) = emit s [] (compile_val v))
∧ (compile (Mat e pes, s) = ARB) (* TODO *)
∧ (compile (Con NONE [c], s) = ARB) (* TODO *)
∧ (compile (Con NONE (c::es), s) = ARB) (* TODO *)
∧ (compile (Con (SOME _) _, s) = ARB) (* Disallowed; use remove_ctors *)
∧ (compile (Proj e n, s) = ARB) (* TODO *)
∧ (compile (Let x e b, s) =
   let (e,s) = compile (e,s) in
   let n = LENGTH s.env in
   let s' = s with env := bind x n s.env in  (* TODO: track size separately? *)
   let (b,s') = compile (b,s') in
   let (r,s') = emit s' (e++b) [Stack Pop] in
   (r, s' with env := s.env))
∧ (compile (Letrec defs b, s) = ARB) (* TODO *)
∧ (compile (Var x, s) =
   case lookup x s.env of
     NONE => ARB (* should not happen *)
   | SOME n => emit s [] [Stack (Load (LENGTH s.env - n))])
∧ (compile (Fun x b, s) = ARB) (* TODO *)
∧ (compile (App Opapp e1 e2, s) = ARB) (* TODO *)
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
  = let (e0,s) = emit s [] [Stack (PushNum 0)] in
    let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    emit s (e0++e1++e2) [Stack Sub;Stack Less])
∧ (compile (App (Opb Leq) e1 e2, s)
  = let (e0,s) = emit s [] [Stack (PushNum 0)] in
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
    let f n1 n2 = [JumpNil n1;Stack (PushNum (bool2num T));Jump n2] in
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

val _ = export_theory ()
