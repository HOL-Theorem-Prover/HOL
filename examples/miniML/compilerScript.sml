open HolKernel bossLib MiniMLTheory listTheory bytecodeTheory lcsymtacs

val _ = new_theory "compiler"

val _ = Hol_datatype`
  compiler_state =
  <|
    next_label: num
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
∧ (compile_val _ = []) (* only allow literals and tupled constructors *)`
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
∧ (compile_opn Divide = []) (* TODO *)
∧ (compile_opn Modulo = []) (* TODO *)`

val offset_def = Define`
  offset len xs = SUM (MAP len xs) + LENGTH xs`

val emit_def = Define`
  emit xs s = (xs, s with next_label := s.next_label + offset s.inst_length xs)`

(* compile : exp * compiler_state → bc_inst list * compiler_state *)
val compile_def = Define`
  (compile (Val v, s) = emit (compile_val v) s)
∧ (compile (App (Opn op) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    emit (e1++e2++(compile_opn op)) s)
∧ (compile (App (Opb Lt) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    emit (e1++e2++[Stack Less]) s)
∧ (compile (App (Opb Geq) e1 e2, s)
  = let (e2,s) = compile (e2,s) in
    let (e1,s) = compile (e1,s) in
    emit (e2++e1++[Stack Less]) s)
∧ (compile (App (Opb Gt) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    emit ([Stack (PushNum 0)]++e1++e2++[Stack Sub;Stack Less]) s)
∧ (compile (App (Opb Leq) e1 e2, s)
  = let (e2,s) = compile (e2,s) in
    let (e1,s) = compile (e1,s) in
    emit ([Stack (PushNum 0)]++e2++e1++[Stack Sub;Stack Less]) s)
∧ (compile (Log And e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    let len = s.inst_length in
    let n   = s.next_label in
    let off = offset len in
    let ljn = len (JumpNil 0)+1 in
    let n1  = n+off e1+ljn+off e2 in
    (e1++[JumpNil n1]++e2, s with next_label := n1))
∧ (compile (Log Or e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    let len = s.inst_length in
    let n   = s.next_label in
    let off = offset len in
    let ljn = len (JumpNil 0)+1 in
    let lp  = len (Stack (PushNum 0)) in
    let lj  = len (Jump 0)+1 in
    let n1  = n+off e1+ljn+lp+lj in
    let n2  = n1+off e2 in
    (e1++[JumpNil n1;Stack (PushNum (bool2num T));Jump n2]++e2,
     s with next_label := n2))
∧ (compile (If e1 e2 e3, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    let (e3,s) = compile (e3,s) in
    let len = s.inst_length in
    let n   = s.next_label in
    let off = offset len in
    let ljn = len (JumpNil 0)+1 in
    let lj  = len (Jump 0)+1 in
    let n1  = n+off e1+ljn+lj in
    let n2  = n1+off e2+lj in
    let n3  = n2+off e3 in
    (e1++[JumpNil n1;Jump n2]++e2++[Jump n3]++e3,
     s with next_label := n3))
∧ (compile (_,s) = ([],s)) (* TODO: rest *)`

val _ = export_theory ()
