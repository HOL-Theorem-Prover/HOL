
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory llistTheory pairTheory finite_mapTheory;
open source_valuesTheory source_syntaxTheory stringTheory lprefix_lubTheory;

val _ = new_theory "source_semantics";


(* types *)

Datatype:
  state = <| funs : dec list        (* all defined functions                         *)
           ; clock : num            (* clock for divergence preservation             *)
           ; input : char llist     (* content of stdin, a potentially infinite list *)
           ; output : char list |>  (* content of stdout, always a finite list       *)
End

Datatype:
  err = TimeOut | Crash
End

Datatype:
  result = Res 'a | Err err
End


(* helper functions for primitive operations etc. *)

Definition return_def:
  return v s = (Res v, s:state)
End

Definition fail_def:
  fail s = (Err Crash, s:state)
End

Definition next_def:
  next s =
    case LHD s of
    | NONE => Num (2 ** 32 - 1) (* EOF *)
    | SOME c => Num (ORD c)
End

(* evaluation of primitive operations *)
Definition eval_op_def:
  eval_op f vs s =
    case (f,vs) of
    | (Add, [Num n1; Num n2]) => return (Num (n1 + n2)) s
    | (Sub, [Num n1; Num n2]) => return (Num (n1 - n2)) s
    | (Div, [Num n1; Num n2]) => if n2 = 0 then fail s else return (Num (n1 DIV n2)) s
    | (Cons, [x; y]) => return (Pair x y) s
    | (Head, [Pair x y]) => return x s
    | (Tail, [Pair x y]) => return y s
    | (Read, []) => return (next s.input)
       (s with input := case LTL s.input of NONE => s.input | SOME t => t)
    | (Write, [Num n]) =>
       (if n < 256 then return (Num 0) (s with output := s.output ++ [CHR n])
        else fail s)
    | _ => fail s
End

Definition take_branch_def:
  take_branch test vs s =
    case (test,vs) of
    | (Equal, [Pair x y; Num 0]) => return F s
    | (Equal, [Num m; Num n]) => return (m = n) s
    | (Less,  [Num m; Num n]) => return (m < n) s
    | _ => fail s
End

Definition empty_env_def:
  empty_env = (λx. NONE) :num -> v option
End

Definition make_env_def:
  make_env [] [] acc = acc ∧
  make_env (x::xs) (y::ys) acc = make_env xs ys ((x =+ SOME y) acc)
End

Definition lookup_fun_def:
  lookup_fun n [] = NONE ∧
  lookup_fun n (Defun k ps body :: rest) =
    if k = n then SOME (ps,body) else lookup_fun n rest
End

Definition env_and_body_def:
  env_and_body n args s =
    case lookup_fun n s.funs of
    | NONE => NONE
    | SOME (params, body) =>
      if LENGTH params ≠ LENGTH args then NONE
      else SOME (make_env params args empty_env, body)
End

(* initially the output is empty *)
Definition init_state_def:
  init_state inp funs =
    <| input := inp; output := ""; funs := funs |>
End


(* definition 1: a big-step relational semantics *)

val _ = set_fixity "--->" (Infixl 489); (* the symbol we will use for the relation *)

Inductive Eval:
  (∀env v s.
    (env, [Const v], s) ---> ([Num v], s))
  ∧
  (∀env n v s.
    env n = SOME v ⇒
    (env, [Var n], s) ---> ([v], s))
  ∧
  (∀env s.
    (env, [], s) ---> ([], s))
  ∧
  (∀env x v y xs vs s1 s2 s3.
    (env, [x], s1) ---> ([v], s2) ∧
    (env, y::xs, s2) ---> (vs, s3) ⇒
    (env, x::y::xs, s1) ---> (v::vs, s3))
  ∧
  (∀env xs vs s1 s2 s3 f v.
    (env, xs, s1) ---> (vs, s2) ∧
    eval_op f vs s2 = (Res v, s3) ⇒
    (env, [Op f xs], s1) ---> ([v], s3))
  ∧
  (∀env x s1 v1 s2 n s3 v2.
    (env, [x], s1) ---> ([v1], s2) ∧
    ((n =+ SOME v1)env, [y], s2) ---> ([v2], s3) ⇒
    (env, [Let n x y], s1) ---> ([v2], s3))
  ∧
  (∀env xs s1 vs s2 test b y z v s3.
    (env, xs, s1) ---> (vs, s2) ∧
    take_branch test vs s2 = (Res b, s2) ∧
    (env, [if b then y else z], s2) ---> ([v], s3) ⇒
    (env, [If test xs y z], s1) ---> ([v], s3))
  ∧
  (∀env xs s1 vs s2 fname v new_env body s3.
    (env, xs, s1) ---> (vs, s2) ∧
    env_and_body fname vs s2 = SOME (new_env, body) ∧
    (new_env, [body], s2) ---> ([v], s3) ⇒
    (env, [Call fname xs], s1) ---> ([v], s3))
End

Inductive app:
  ∀fname vs s1 v s2 new_env body.
    env_and_body fname vs s1 = SOME (new_env, body) ∧
    (new_env, [body], s1) ---> ([v], s2) ⇒
    app fname vs s1 (v,s2)
End

Theorem Eval_Call:
  ∀env xs s1 vs s2 fname v s3.
    (env, xs, s1) ---> (vs, s2) ∧
    app fname vs s2 (v,s3) ⇒
    (env, [Call fname xs], s1) ---> ([v], s3)
Proof
  rw [] \\ once_rewrite_tac [Eval_cases] \\ fs []
  \\ goal_assum (first_assum o mp_then.mp_then mp_then.Any mp_tac)
  \\ fs [app_cases]
QED

val _ = set_fixity "prog_terminates" (Infixl 480);

Definition prog_terminates_def:
  (input, Program funs main) prog_terminates output =
    ∃s r. (empty_env, [main], init_state input funs) ---> (r, s) ∧
          output = s.output
End

Overload prog_terminates =
  “λ(input:string,p) output. (fromList input,p) prog_terminates output”;


(* definition 2: a functional big-step semantics *)

Definition get_env_and_body_def:
  get_env_and_body fname args s =
    case env_and_body fname args s of
    | NONE => fail s
    | SOME (env, body) =>
      if s.clock = 0 then (Err TimeOut, s)
      else (Res (env, body), s with clock := s.clock - 1)
End

Definition fix_def: (* helps prove termination of the definition of eval *)
  fix s x =
    if (SND x).clock ≤ s.clock then x
    else (FST x, SND x with clock := s.clock)
End

(* evaluation of expressions and expression lists *)
Definition eval_def:
  eval (env:num -> v option) (Const n) s = (Res (Num n), s) ∧
  eval env (Var t) s =
    (case env t of
     | NONE => (Err Crash, s)
     | SOME v => (Res v, s)) ∧
  eval env (Op f xs) s =
    (case evals env xs s of
     | (Err e, s) => (Err e, s)
     | (Res vs, s1) => eval_op f vs s1) ∧
  eval env (Let t x y) s =
    (case fix s (eval env x s) of
     | (Err e, s1) => (Err e, s1)
     | (Res v, s1) => eval ((t =+ SOME v) env) y s1) ∧
  eval env (If test xs y z) s =
    (case fix s (evals env xs s) of
     | (Err e, s1) => (Err e, s1)
     | (Res vs, s1) =>
       case take_branch test vs s1 of
       | (Res b, s1) => eval env (if b then y else z) s1
       | (Err e, s1) => (Err e, s1)) ∧
  eval env (Call t xs) s =
    (case fix s (evals env xs s) of
     | (Err e, s1) => (Err e, s1)
     | (Res vs, s1) =>
       case get_env_and_body t vs s1 of
       | (Err e,s2) => (Err e, s2)
       | (Res (new_env, body), s2) => eval new_env body s2) ∧
  evals env [] s = (Res [], s) ∧
  evals env (x::xs) s =
    (case fix s (eval env x s) of
     | (Err v, s1) => (Err v, s1)
     | (Res v, s1) =>
       case evals env xs s1 of
       | (Err v, s2) => (Err v, s2)
       | (Res vs, s2) => (Res (v::vs), s2))
Termination
  WF_REL_TAC ‘inv_image (measure I LEX measure I)
                (λx. case x of INL (env,x,s) => (s.clock,exp_size x)
                             | INR (env,xs,s) => (s.clock,exp1_size xs))’
  \\ rw [] \\ fs [fix_def,CaseEq"bool"] \\ rw [] \\ fs []
  \\ fs [take_branch_def,AllCaseEqs(),return_def,fail_def,get_env_and_body_def]
  \\ rw [] \\ fs []
End

Theorem eval_clock:
  (∀env x s res s'. eval env x s = (res,s') ⇒ s'.clock ≤ s.clock) ∧
  (∀env xs s res s'. evals env xs s = (res,s') ⇒ s'.clock ≤ s.clock)
Proof
  ho_match_mp_tac eval_ind \\ rw [eval_def]
  \\ fs [AllCaseEqs(),get_env_and_body_def,eval_op_def,fix_def,return_def,fail_def]
  \\ rw [] \\ fs []
  \\ fs [AllCaseEqs(),take_branch_def,return_def,fail_def]
  \\ rw [] \\ fs []
QED

Triviality fix_eval:
  fix s (eval env x s) = eval env x s ∧
  fix s (evals env xs s) = evals env xs s
Proof
  Cases_on ‘eval env x s’ \\ Cases_on ‘evals env xs s’ \\ fs []
  \\ imp_res_tac eval_clock \\ fs [fix_def]
QED

Theorem eval_def[allow_rebind]  = REWRITE_RULE [fix_eval] eval_def;
Theorem eval_ind[allow_rebind]  = REWRITE_RULE [fix_eval] eval_ind;
Theorem evals_ind = REWRITE_RULE [fix_eval] eval_ind
  |> Q.SPECL [‘λenv x s. P env [x] s’,‘P’]
  |> CONV_RULE (DEPTH_CONV BETA_CONV)
  |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL;

(* monadic formulation of eval_def *)

Type M = ``:state -> 'a result # state``

Definition bind_def:
  bind f g s =
    case f s of
    | (Res res, s1) => g res s1
    | (Err e, s1) => (Err e, s1)
End

Overload monad_unitbind[local] = ``bind``
Overload monad_bind[local] = ``bind``
Overload return[local] = ``return``

val _ = monadsyntax.add_monadsyntax()

Theorem eval_thm:
  eval env (Const n) =
    return (Num n) ∧
  eval env (Var vname) =
    (case env vname of
     | NONE => fail
     | SOME v => return v) ∧
  eval env (Op f xs) =
    do vs <- evals env xs;
       eval_op f vs od ∧
  eval env (Let vname x y) =
    do v <- eval env x;
       eval ((vname =+ SOME v)env) y od ∧
  eval env (If test xs y z) =
    do vs <- evals env xs;
       b <- take_branch test vs;
       eval env (if b then y else z) od ∧
  eval env (Call fname xs) =
    do vs <- evals env xs;
       (new_env,body) <- get_env_and_body fname vs;
       eval new_env body od ∧
  evals env [] =
    return [] ∧
  evals env (x::xs) =
    do v <- eval env x;
       vs <- evals env xs;
       return (v::vs) od
Proof
  fs [FUN_EQ_THM,eval_def,bind_def,return_def,fail_def,take_branch_def]
  \\ rw [] \\ BasicProvers.every_case_tac \\ fs [fail_def,return_def,fail_def]
QED

Definition eval_from_def:
  eval_from k input (Program funs main) =
    eval empty_env main (init_state input funs with clock := k)
End

Definition prog_avoids_crash_def:
  prog_avoids_crash input prog =
    ∀k res s. eval_from k input prog = (res, s) ⇒ res ≠ Err Crash
End

Definition prog_timesout_def:
  prog_timesout k input prog =
    ∃s. eval_from k input prog = (Err TimeOut, s)
End

Definition prog_output_def:
  prog_output k input prog =
    let (res,s) = eval_from k input prog in
      fromList s.output
End

val _ = set_fixity "prog_diverges" (Infixl 480);

Definition prog_diverges_def:
  (input, prog) prog_diverges output ⇔
    (∀k. prog_timesout k input prog) ∧
    output = build_lprefix_lub { prog_output k input prog | k IN UNIV }
End

val _ = export_theory();
