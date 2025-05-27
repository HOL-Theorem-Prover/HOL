(*===========================================================================*)
(* Nice monad example from Ramana Kumar                                      *)
(*===========================================================================*)

open HolKernel boolLib bossLib Parse stringTheory monadsyntax
     pairTheory rich_listTheory alistTheory arithmeticTheory

val _ = new_theory "awe";

Datatype:
  call_target
  = IntCall string
  | ExtCall string
End

Datatype:
  expr
  = Name string
  | IfExp expr expr expr
  | Subscript expr expr
  | Attribute expr string
  | Call call_target (expr list)
End

Datatype:
  base_assignment_target
  = NameTarget string
  | TopLevelNameTarget string
  | SubscriptTarget base_assignment_target expr
  | AttributeTarget base_assignment_target string
End

Datatype:
  stmt
  = Pass
  | Expr expr
  | For string expr num (stmt list)
  | If expr (stmt list) (stmt list)
  | Assert expr string
  | Raise string
  | Return (expr option)
  | AugAssign base_assignment_target expr
End

Definition return_def:
  return x (s:num) = (INL x, s)
End

Definition raise_def:
  raise (e:string) (s:num) = (INR e, s)
End

Definition bind_def:
  bind f g (s:num) =
  case f s of (INL x, s) => g x s | (INR (e:string), (s:num)) => (INR e, s)
End

Definition ignore_bind_def:
  ignore_bind f g = bind f (λx. g)
End

val () = declare_monad ("awe",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “raise”, guard = NONE
  });
val () = enable_monad "awe";
val () = enable_monadsyntax();

Definition lift_option_def:
  lift_option x str =
    case x of SOME v => return v | NONE => raise str
End

Theorem SUM_MAP_FILTER_MEM_LE:
  MEM x ls /\ ~P x ==>
  SUM (MAP f (FILTER P ls)) + f x <= SUM (MAP f ls)
Proof
  qid_spec_tac`x`
  \\ Induct_on`ls`
  \\ rw[] \\ gs[]
  >- (
    irule SUM_SUBLIST \\ simp[]
    \\ irule MAP_SUBLIST \\ simp[]
    \\ irule FILTER_sublist )
  \\ first_x_assum drule \\ rw[]
QED

Definition bound_def:
  stmt_bound ts Pass = 0n ∧
  stmt_bound ts (Return NONE) = 0 ∧
  stmt_bound ts (Return (SOME e)) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Raise _) = 0 ∧
  stmt_bound ts (Assert e _) =
    1 + expr_bound ts e ∧
  stmt_bound ts (AugAssign bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  stmt_bound ts (If e ss1 ss2) =
    1 + expr_bound ts e +
     MAX (stmts_bound ts ss1)
         (stmts_bound ts ss2) ∧
  stmt_bound ts (For _ e n ss) =
    1 + expr_bound ts e +
    1 + n + n * (stmts_bound ts ss) ∧
  stmt_bound ts (Expr e) =
    1 + expr_bound ts e ∧
  stmts_bound ts [] = 0 ∧
  stmts_bound ts (s::ss) =
    1 + stmt_bound ts s
      + stmts_bound ts ss ∧
  base_target_bound ts (NameTarget _) = 0 ∧
  base_target_bound ts (TopLevelNameTarget _) = 0 ∧
  base_target_bound ts (AttributeTarget bt _) =
    1 + base_target_bound ts bt ∧
  base_target_bound ts (SubscriptTarget bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  expr_bound ts (Name _) = 0 ∧
  expr_bound ts (IfExp e1 e2 e3) =
    1 + expr_bound ts e1
      + MAX (expr_bound ts e2)
            (expr_bound ts e3) ∧
  expr_bound ts (Subscript e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  expr_bound ts (Attribute e _) =
    1 + expr_bound ts e ∧
  expr_bound ts (Call (IntCall fn) es) =
    1 + exprs_bound ts es
      + (case ALOOKUP ts fn of NONE => 0 |
         SOME ss => stmts_bound (ADELKEY fn ts) ss) ∧
  expr_bound ts (Call t es) =
    1 + exprs_bound ts es ∧
  exprs_bound ts [] = 0 ∧
  exprs_bound ts (e::es) =
    1 + expr_bound ts e
      + exprs_bound ts es
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (ts, es)))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size expr_size es
  | INR (INR (INR (INL (ts, e)))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      expr_size e
  | INR (INR (INL (ts, bt))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      base_assignment_target_size bt
  | INR (INL (ts, ss)) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size stmt_size ss
  | INL (ts, s) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      stmt_size s)’
  \\ rw[]
  \\ drule ALOOKUP_MEM
  \\ rw[ADELKEY_def]
  \\ qmatch_goalsub_abbrev_tac`MAP f (FILTER P ts)`
  \\ drule_then(qspecl_then[`f`,`P`]mp_tac) SUM_MAP_FILTER_MEM_LE
  \\ simp[Abbr`P`, Abbr`f`]
End

val option_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="option",Tyop="option"}));

Datatype:
  evaluation_context = <|
    stk: string list
  ; target: string
  ; sources: (string, num list) alist
  |>
End

Definition get_self_code_def:
  get_self_code cx = ALOOKUP cx.sources cx.target
End

Definition dest_Internal_FunctionDef_def:
  dest_Internal_FunctionDef 0 = [("", [Pass])] ∧
  dest_Internal_FunctionDef _ = []
End

Definition remcode_def:
  remcode cx =
  case get_self_code cx of NONE => []
     | SOME ts => FILTER (λ(fn,ss). ¬MEM fn cx.stk)
          (FLAT (MAP dest_Internal_FunctionDef ts))
End

Definition push_function_def:
  push_function fn (sc:num) cx st =
  return (cx with stk updated_by CONS fn) $ st
End

Datatype:
  value
  = NoneV
  | BoolV bool
  | StringV num string
End

Datatype:
  subscript
  = IntSubscript num
  | StrSubscript string
End

Theorem bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ==> g x t = g' x t)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule \\ goal_assum drule
QED

Theorem ignore_bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ⇒ g t = g' t)
  ⇒
  ignore_bind f g = ignore_bind f' g'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong_implicit
  \\ rw[]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

val _ = set_trace "TFL rewrite monitoring" 3;

Definition evaluate_def:
  eval_stmt cx (AugAssign t e) = do
    eval_base_target cx t;
    tv <- eval_expr cx e;
    return ()
  od ∧
  eval_stmt cx (For id e n body) = do
    eval_expr cx e;
    vs <- raise "For not ArrayV";
    eval_for cx id body vs
  od ∧
  eval_stmt cx _ = return () ∧
  eval_stmts cx [] = return () ∧
  eval_stmts cx (s::ss) = do
    eval_stmt cx s;
    eval_stmts cx ss
  od ∧
  eval_base_target cx (SubscriptTarget t e) = do
    (loc, sbs) <- eval_base_target cx t;
    eval_expr cx e;
    return $ (loc, IntSubscript 0 :: sbs)
  od ∧
  eval_base_target cx _ = return $ ("", []) ∧
  eval_for cx nm body [] = return () ∧
  eval_for cx nm body ((v:value)::vs) = do
    eval_stmts cx body;
    eval_for cx nm body vs
  od ∧
  eval_expr cx (Call (IntCall fn) es) = do
    (* check (¬MEM fn cx.stk) "recursion"; *)
    ts <- lift_option (get_self_code cx) "IntCall get_self_code";
    (tup:(value list # num # stmt list)) <- raise "IntCall lookup_function";
    args <<- FST tup;
    body <<- SND $ SND tup;
    vs <- eval_exprs cx es;
    env <- raise "IntCall bind_arguments";
    cxf <- push_function fn env cx;
    eval_stmts cxf body;
    return $ NoneV
  od ∧
  eval_expr cx _ = return $ NoneV ∧
  eval_exprs cx [] = return [] ∧
  eval_exprs cx (e::es) = do
    tv <- eval_expr cx e;
    vs <- eval_exprs cx es;
    return $ NoneV::vs
  od
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (INR (cx, es)))))
    => exprs_bound (remcode cx) es
  | INR (INR (INR (INR (INL (cx, e)))))
    => expr_bound (remcode cx) e
  | INR (INR (INR (INL (cx, nm, body, vs))))
    => 1 + LENGTH vs + (LENGTH vs) * (stmts_bound (remcode cx) body)
  | INR (INR (INL (cx, t)))
    => base_target_bound (remcode cx) t
  | INR (INL (cx, ss)) => stmts_bound (remcode cx) ss
  | INL (cx, s) => stmt_bound (remcode cx) s)’
  \\ reverse(rw[bound_def, MAX_DEF, MULT])
  >- gvs[raise_def]
  \\ gvs[]
  \\ gvs[push_function_def, return_def]
  \\ gvs[lift_option_def, CaseEq"option", CaseEq"prod", option_CASE_rator,
         raise_def, return_def]
End

val () = export_theory();
