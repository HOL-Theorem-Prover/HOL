open HolKernel MiniMLTheory listTheory bytecodeTheory lcsymtacs

val _ = new_theory "compiler"

val _ = Hol_datatype`
  compiler_state =
  <|
    dummy: unit
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
∧ (compile_opn Modulo = []) (* TODO *)`;

(* compile : exp * compiler_state → bc_inst list * compiler_state *)
val compile_def = Define`
  (compile (Val v, s) = (compile_val v, s))
∧ (compile (App (Opn op) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    (e1++e2++(compile_opn op),s))
∧ (compile (App (Opb Lt) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    (e1++e2++[Stack Less],s))
∧ (compile (App (Opb Geq) e1 e2, s)
  = let (e2,s) = compile (e2,s) in
    let (e1,s) = compile (e1,s) in
    (e2++e1++[Stack Less],s))
∧ (compile (App (Opb Gt) e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    ([Stack (PushNum 0)]++e1++e2++[Stack Sub;Stack Less],s))
∧ (compile (App (Opb Leq) e1 e2, s)
  = let (e2,s) = compile (e2,s) in
    let (e1,s) = compile (e1,s) in
    ([Stack (PushNum 0)]++e2++e1++[Stack Sub;Stack Less],s))
∧ (compile (Log And e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    (* TODO: need proper offsets *)
    (e1++[JumpNil (0+LENGTH e1+LENGTH e2)]++e2, s))
∧ (compile (Log Or e1 e2, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    (* TODO: need proper offsets *)
    let n = 0+LENGTH e1+2 in
    (e1++[JumpNil n;Jump (n+LENGTH e2)]++e2, s))
∧ (compile (If e1 e2 e3, s)
  = let (e1,s) = compile (e1,s) in
    let (e2,s) = compile (e2,s) in
    let (e3,s) = compile (e3,s) in
    let n1 = 0+LENGTH e1+2 in
    let n2 = n1+LENGTH e2+1 in
    (* TODO: need proper offsets *)
    (e1++[JumpNil n1;Jump n2]++e2++[Jump (n2+LENGTH e3)]++e3, s))
∧ (compile (_,s) = ([],s)) (* TODO: rest *)`

val _ = export_theory ()
