
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory source_semanticsTheory codegenTheory
     source_propertiesTheory mp_then parsingTheory x64asm_syntaxTheory
     wordsTheory wordsLib;

val _ = new_theory "automation_lemmas";


(* theorems used in proof automation *)

Theorem trans_app:
  ∀n params vs.
    let env = make_env params vs empty_env in
      (b ⇒ (env,[body],s) ---> ([v],s1)) ⇒
      LENGTH params = LENGTH vs ⇒
      lookup_fun (name n) s.funs = SOME (params,body) ⇒
      b ⇒ app (name n) vs s (v,s1)
Proof
  fs [app_cases,env_and_body_def]
QED

Theorem trans_Call:
  (b1 ⇒ (env, xs, s1) ---> (vs, s2)) ∧
  (b2 ⇒ app fname vs s2 (v,s3)) ⇒
  (b1 ∧ b2 ⇒ (env, [Call fname xs], s1) ---> ([v], s3))
Proof
  metis_tac [Eval_Call]
QED

Theorem trans_Var:
  ∀n v. env (name n) = SOME v ⇒ (env,[Var (name n)],s) ---> ([v],s)
Proof
  fs [Eval_rules]
QED

Theorem trans_nil:
  (T ⇒ (env, [], s) ---> ([], s))
Proof
  rw [] \\ metis_tac [Eval_rules]
QED

Theorem trans_cons:
  (b1 ⇒ (env, [x], s1) ---> ([v], s2)) ∧
  (b2 ⇒ (env, xs, s2) ---> (vs, s3)) ⇒
  (b1 ∧ b2 ⇒ (env, x::xs, s1) ---> (v::vs, s3))
Proof
  Cases_on ‘xs’ \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac Eval_length \\ fs [] \\ rw []
  \\ pop_assum mp_tac
  THEN1 simp [Once Eval_cases]
  \\ Cases_on ‘vs’ \\ fs []
  \\ simp [Once Eval_cases] \\ metis_tac []
QED

Theorem auto_let:
  (b1 ⇒ (env, [x_1], s1) ---> ([(a:'a->v) v1], s2)) ∧
  (∀v1. b2 v1 ⇒ ((name let_n =+ SOME (a v1)) env, [y_1], s2) ---> ([b (f v1)], s3)) ⇒
  (b1 ∧ b2 v1 ⇒
    (env, [Let (name let_n) x_1 y_1], s1) ---> ([(b:'b->v) (LET f v1)], s3))
Proof
  rw [LET_THM,Eval_eq] \\ metis_tac []
QED

Theorem auto_otherwise:
  (b1 ⇒ (env, [x_1], s) ---> ([(a:'a->v) v1], s)) ⇒
  (b1 ⇒ (env, [If Less [Const 0; Const 1] x_1 (Const 0)], s) --->
        ([(a:'a->v) (otherwise v1)], s))
Proof
  fs [Eval_eq,take_branch_def,return_def]
QED

(* bool *)

Theorem auto_bool_F:
  T ⇒ (env,[Const 0],s) ---> ([bool F],s)
Proof
  fs [Eval_eq]
QED

Theorem auto_bool_T:
  T ⇒ (env,[Const 1],s) ---> ([bool T],s)
Proof
  fs [Eval_eq]
QED

Theorem auto_bool_not:
  (b0 ⇒ (env,[x1],s) ---> ([bool b],s)) ⇒
  b0 ⇒ (env,[Op Sub [Const 1; x1]],s) ---> ([bool (~b)],s)
Proof
  rw [Eval_eq,PULL_EXISTS] \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ Cases_on ‘b’ \\ EVAL_TAC
QED

Theorem auto_bool_and:
  (b0 ⇒ (env,[x1],s) ---> ([bool bA],s)) ∧
  (b1 ⇒ (env,[x2],s) ---> ([bool bB],s)) ⇒
  b0 ∧ b1 ⇒ (env,[Op Sub [Op Add [x1; x2]; Const 1]],s) ---> ([bool (bA ∧ bB)],s)
Proof
  rw [Eval_eq,PULL_EXISTS] \\ fs []
  \\ rpt (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ Cases_on ‘bA’ \\ Cases_on ‘bB’ \\ EVAL_TAC \\ fs [AllCaseEqs()]
QED

Theorem auto_bool_iff:
  (b0 ⇒ (env,[x1],s) ---> ([bool bA],s)) ∧
  (b1 ⇒ (env,[x2],s) ---> ([bool bB],s)) ⇒
  b0 ∧ b1 ⇒
  (env,[If Equal [x1; x2] (Const 1) (Const 0)],s) ---> ([bool (bA ⇔ bB)],s)
Proof
  rw [Eval_eq,PULL_EXISTS] \\ fs []
  \\ rpt (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ Cases_on ‘bA’ \\ Cases_on ‘bB’ \\ EVAL_TAC \\ fs [AllCaseEqs(),Eval_eq]
QED

Theorem last_bool_if:
  (b0 ⇒ (env,[x_g],s) ---> ([bool b],s)) ∧
  (b2 ⇒ (env,[x_t],s) ---> ([a t],s)) ∧
  (b3 ⇒ (env,[x_f],s) ---> ([a f],s)) ⇒
  b0 ∧ (if b then b2 else b3) ⇒
  (env,[If Equal [x_g; Const 1] x_t x_f],s) ---> ([a (if b then t else f)],s)
Proof
  fs [Eval_eq,PULL_EXISTS,take_branch_def,AllCaseEqs(),return_def,fail_def]
  \\ Cases_on ‘b’ \\ fs [] \\ metis_tac [EVAL “1=0:num”]
QED

(* num *)

Theorem auto_num_const:
  (T ⇒ (env, [Const 0], s) ---> ([Num 0], s)) ∧
  (T ⇒ (env, [Const (NUMERAL n)], s) ---> ([Num (NUMERAL n)], s))
Proof
  fs [Eval_eq]
QED

Theorem auto_num_add:
  (b0 ⇒ (env,[x1],s0) ---> ([Num n1],s1)) ∧
  (b1 ⇒ (env,[x2],s1) ---> ([Num n2],s2)) ⇒
  b0 ∧ b1 ⇒ (env,[Op Add [x1; x2]],s0) ---> ([Num (n1 + n2)],s2)
Proof
  fs [Eval_eq,PULL_EXISTS,eval_op_def,AllCaseEqs(),return_def,fail_def]
  \\ metis_tac []
QED

Theorem auto_num_sub:
  (b0 ⇒ (env,[x1],s0) ---> ([Num n1],s1)) ∧
  (b1 ⇒ (env,[x2],s1) ---> ([Num n2],s2)) ⇒
  b0 ∧ b1 ⇒ (env,[Op Sub [x1; x2]],s0) ---> ([Num (n1 − n2)],s2)
Proof
  fs [Eval_eq,PULL_EXISTS,eval_op_def,AllCaseEqs(),return_def,fail_def]
  \\ metis_tac []
QED

Theorem auto_num_div:
  (b0 ⇒ (env,[x1],s0) ---> ([Num n1],s1)) ∧
  (b1 ⇒ (env,[x2],s1) ---> ([Num n2],s2)) ⇒
  b0 ∧ b1 ∧ n2 ≠ 0 ⇒ (env,[Op Div [x1; x2]],s0) ---> ([Num (n1 DIV n2)],s2)
Proof
  fs [Eval_eq,PULL_EXISTS,eval_op_def,AllCaseEqs(),return_def,fail_def]
  \\ metis_tac []
QED

Theorem auto_num_if_eq:
  (b0 ⇒ (env,[x1],s) ---> ([Num n1],s)) ∧
  (b1 ⇒ (env,[x2],s) ---> ([Num n2],s)) ∧
  (b2 ⇒ (env,[y],s) ---> ([a t],s)) ∧
  (b3 ⇒ (env,[z],s) ---> ([a f],s)) ⇒
  b0 ∧ b1 ∧ (if n1 = n2 then b2 else b3) ⇒
  (env,[If Equal [x1; x2] y z],s) ---> ([a (if n1 = n2 then t else f)],s)
Proof
  fs [Eval_eq,PULL_EXISTS,take_branch_def,AllCaseEqs(),return_def,fail_def]
  \\ metis_tac []
QED

Theorem auto_num_if_less:
  (b0 ⇒ (env,[x1],s) ---> ([Num n1],s)) ∧
  (b1 ⇒ (env,[x2],s) ---> ([Num n2],s)) ∧
  (b2 ⇒ (env,[y],s) ---> ([a t],s)) ∧
  (b3 ⇒ (env,[z],s) ---> ([a f],s)) ⇒
  b0 ∧ b1 ∧ (if n1 < n2 then b2 else b3) ⇒
  (env,[If Less [x1; x2] y z],s) ---> ([a (if n1 < n2 then t else f)],s)
Proof
  fs [Eval_eq,PULL_EXISTS,take_branch_def,AllCaseEqs(),return_def,fail_def]
  \\ metis_tac []
QED

(* list *)

Theorem auto_list_nil:
  T ⇒ (env,[Const 0],s) ---> ([list a []],s)
Proof
  fs [Eval_eq]
QED

Theorem auto_list_cons:
  (b0 ⇒ (env,[x1],s) ---> ([a x],s)) ∧
  (b1 ⇒ (env,[x2],s) ---> ([list a xs],s)) ⇒
  b0 ∧ b1 ⇒
  (env,[Op Cons [x1; x2]],s) ---> ([list a (x::xs)],s)
Proof
  fs [Eval_eq,eval_op_def,PULL_EXISTS,AllCaseEqs(),fail_def,return_def]
  \\ metis_tac []
QED

Theorem auto_list_case:
  (b0 ⇒ (env,[x0],s) ---> ([list (a:'a->v) v0],s)) ∧
  (b1 ⇒ (env,[x1],s) ---> ([(b:'b->v) v1],s)) ∧
  (∀y1 y2.
     b2 y1 y2 ⇒
     (env⦇name n2 ↦ SOME (list a y2); name n1 ↦ SOME (a y1)⦈,[x2],s) --->
     ([b (v2 y1 y2)],s)) ⇒
  ALL_DISTINCT ([name n1] ++ free_vars x0) ∧
  b0 ∧ (v0 = [] ⇒ b1) /\ (∀y1 y2. v0 = y1::y2 ⇒ b2 y1 y2) ⇒
  (env,[If Equal [x0; Const 0] x1
         (Let (name n1) (Op Head [x0])
            (Let (name n2) (Op Tail [x0]) x2))],s) --->
  ([b (list_CASE v0 v1 v2)],s)
Proof
  Cases_on ‘v0’ \\ fs [] \\ rw [] \\ fs []
  \\ rpt (fs [Eval_eq,PULL_EXISTS,eval_op_def,AllCaseEqs(),fail_def,
              take_branch_def,return_def,name_def]
          \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
QED

(* option *)

Theorem auto_option_none:
  T ⇒ (env,[Const 0],s) ---> ([option a NONE],s)
Proof
  fs [Eval_eq]
QED

Theorem auto_option_some:
  (b0 ⇒ (env,[x1],s) ---> ([a x],s)) ⇒
  b0 ⇒
  (env,[Op Cons [x1; Const 0]],s) ---> ([option a (SOME x)],s)
Proof
  fs [Eval_eq,eval_op_def,PULL_EXISTS,AllCaseEqs(),fail_def,return_def]
  \\ metis_tac []
QED

Theorem auto_option_case:
  (b0 ⇒ (env,[x0],s) ---> ([option (a:'a->v) v0],s)) ∧
  (b1 ⇒ (env,[x1],s) ---> ([(b:'b->v) v1],s)) ∧
  (∀y1. b2 y1 ⇒ (env⦇name n ↦ SOME (a y1)⦈,[x2],s) ---> ([b (v2 y1)],s)) ⇒
  b0 ∧ (v0 = NONE ⇒ b1) /\ (∀y1. v0 = SOME y1 ==> b2 y1) ⇒
  (env,[If Equal [x0; Const 0] x1
         (Let (name n) (Op Head [x0]) x2)],s) --->
  ([b (option_CASE v0 v1 v2)],s)
Proof
  Cases_on ‘v0’ \\ fs [] \\ rw [] \\ fs []
  \\ rpt (fs [Eval_eq,PULL_EXISTS,eval_op_def,AllCaseEqs(),fail_def,
              take_branch_def,return_def,name_def]
          \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
QED

(* pair *)

Theorem auto_pair_fst:
  (b0 ⇒ (env,[x1],s) ---> ([pair a b x],s)) ⇒
  b0 ⇒ (env,[Op Head [x1]],s) ---> ([a (FST x)],s)
Proof
  Cases_on ‘x’ \\ fs [Eval_eq,eval_op_def,PULL_EXISTS,AllCaseEqs(),fail_def,return_def]
  \\ metis_tac []
QED

Theorem auto_pair_snd:
  (b0 ⇒ (env,[x1],s) ---> ([pair a b x],s)) ⇒
  b0 ⇒ (env,[Op Tail [x1]],s) ---> ([b (SND x)],s)
Proof
  Cases_on ‘x’ \\ fs [Eval_eq,eval_op_def,PULL_EXISTS,AllCaseEqs(),fail_def,return_def]
  \\ metis_tac []
QED

Theorem auto_pair_cons:
  (b0 ⇒ (env,[x1],s) ---> ([a x],s)) ∧
  (b1 ⇒ (env,[x2],s) ---> ([b y],s)) ⇒
  b0 ∧ b1 ⇒
  (env,[Op Cons [x1; x2]],s) ---> ([pair a b (x,y)],s)
Proof
  fs [Eval_eq,eval_op_def,PULL_EXISTS,AllCaseEqs(),fail_def,return_def]
  \\ metis_tac []
QED

Theorem auto_pair_case:
  (b0 ⇒ (env,[x0],s) ---> ([pair (a:'a->v) (b:'b->v) v0],s)) ∧
  (∀y1 y2.
     b1 y1 y2 ⇒
     (env⦇name n2 ↦ SOME (b y2); name n1 ↦ SOME (a y1)⦈,[x1],s) --->
     ([(c:'c->v) (v1 y1 y2)],s)) ⇒
  ALL_DISTINCT ([name n1; name n2] ++ free_vars x0) ∧
  b0 ∧ (∀y1 y2. v0 = (y1,y2) ⇒ b1 y1 y2) ⇒
  (env,[Let (name n1) (Op Head [x0])
         (Let (name n2) (Op Tail [x0]) x1)],s) --->
  ([c (pair_CASE v0 v1)],s)
Proof
  Cases_on ‘v0’ \\ fs [] \\ rw [] \\ fs []
  \\ rpt (fs [Eval_eq,PULL_EXISTS,eval_op_def,AllCaseEqs(),fail_def,
              take_branch_def,return_def,name_def]
          \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
QED

(* v -- we use deep embedding to be able to support isNum *)

Definition deep_def[simp]:
  deep (Num n) = cons (bool T) (Num n) ∧
  deep (Pair x y) = cons (bool F) (cons (deep x) (deep y))
End

Theorem auto_v_Num:
  (b0 ⇒ (env,[x1],s) ---> ([Num n],s)) ⇒
  b0 ⇒
  (env,[Op Cons [Const 1; x1]],s) ---> ([deep (Num n)],s)
Proof
  rw [] \\ fs [Eval_eq,PULL_EXISTS,eval_op_def,return_def,AllCaseEqs(),fail_def]
QED

Theorem auto_v_Pair:
  (b0 ⇒ (env,[x1],s) ---> ([deep x],s)) ∧
  (b1 ⇒ (env,[x2],s) ---> ([deep y],s)) ⇒
  b0 ∧ b1 ⇒
  (env,[Op Cons [Const 0; Op Cons [x1; x2]]],s) ---> ([deep (Pair x y)],s)
Proof
  rw [] \\ fs [Eval_eq,PULL_EXISTS,eval_op_def,return_def,AllCaseEqs(),fail_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
QED

Theorem auto_v_isNum:
  (b0 ⇒ (env,[x1],s) ---> ([deep x],s)) ⇒
  b0 ⇒
  (env,[Op Head [x1]],s) ---> ([bool (isNum x)],s)
Proof
  Cases_on ‘x’ \\ fs [] \\ rw []
  \\ fs [Eval_eq,PULL_EXISTS,eval_op_def,return_def,AllCaseEqs(),fail_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
QED

Theorem auto_v_getNum:
  (b0 ⇒ (env,[x1],s) ---> ([deep x],s)) ⇒
  b0 ⇒
  (env,[If Equal [Op Head [x1]; Const 0]
          (Const 0) (Op Tail [x1])],s) ---> ([Num (getNum x)],s)
Proof
  Cases_on ‘x’ \\ fs [] \\ rw []
  \\ fs [Eval_eq,PULL_EXISTS,eval_op_def,return_def,AllCaseEqs(),fail_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [take_branch_def,return_def]
  \\ fs [Eval_eq,PULL_EXISTS,eval_op_def,return_def,AllCaseEqs(),fail_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
QED

Theorem auto_v_head[local]:
  lookup_fun (name "h") s.funs =
    SOME ([name "x"],
          If Equal [Op Head [Var (name "x")]; Const 1]
            (Var (name "x")) (Op Head [Op Tail [Var (name "x")]])) ⇒
  (b0 ⇒ (env,[x1],s) ---> ([deep x],s)) ⇒
  b0 ⇒
  (env,[Call (name "h") [x1]],s) ---> ([deep (head x)],s)
Proof
  Cases_on ‘x’ \\ fs [] \\ rw []
  \\ fs [Eval_eq,PULL_EXISTS,eval_op_def,return_def,AllCaseEqs(),
         fail_def,app_cases,env_and_body_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [take_branch_def,return_def,combinTheory.APPLY_UPDATE_THM,
         make_env_def,Eval_eq,PULL_EXISTS,eval_op_def,return_def,
         AllCaseEqs(),fail_def,combinTheory.APPLY_UPDATE_THM]
QED

Theorem auto_v_tail[local]:
  lookup_fun (name "t") s.funs =
    SOME ([name "x"],
          If Equal [Op Head [Var (name "x")]; Const 1]
            (Var (name "x")) (Op Tail [Op Tail [Var (name "x")]])) ⇒
  (b0 ⇒ (env,[x1],s) ---> ([deep x],s)) ⇒
  b0 ⇒
  (env,[Call (name "t") [x1]],s) ---> ([deep (tail x)],s)
Proof
  Cases_on ‘x’ \\ fs [] \\ rw []
  \\ fs [Eval_eq,PULL_EXISTS,eval_op_def,return_def,AllCaseEqs(),
         fail_def,app_cases,env_and_body_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [take_branch_def,return_def,combinTheory.APPLY_UPDATE_THM,
         make_env_def,Eval_eq,PULL_EXISTS,eval_op_def,return_def,
         AllCaseEqs(),fail_def,combinTheory.APPLY_UPDATE_THM]
QED

Theorem auto_v_head = auto_v_head |> UNDISCH;
Theorem auto_v_tail = auto_v_tail |> UNDISCH;

(* char *)

Theorem auto_char_CHR:
  (b0 ⇒ (env,[x1],s) ---> ([Num x],s)) ⇒
  b0 ∧ x < 256 ⇒ (env,[x1],s) ---> ([char (CHR x)],s)
Proof
  fs [char_def]
QED

Theorem auto_char_ORD:
  (b0 ⇒ (env,[x1],s) ---> ([char x],s)) ⇒
  b0 ⇒ (env,[x1],s) ---> ([Num (ORD x)],s)
Proof
  fs [char_def]
QED

(* word *)

Definition word_def:
  word w = Num (w2n w)
End

Theorem auto_word4_n2w:
  (b0 ⇒ (env,[x1],s) ---> ([Num x],s)) ⇒
  b0 ∧ x < 16 ⇒ (env,[x1],s) ---> ([word ((n2w x):word4)],s)
Proof
  fs [word_def]
QED

Theorem auto_word64_n2w:
  (b0 ⇒ (env,[x1],s) ---> ([Num x],s)) ⇒
  b0 ∧ x < 2 ** 64 ⇒ (env,[x1],s) ---> ([word ((n2w x):word64)],s)
Proof
  fs [word_def]
QED

Theorem auto_word4_w2n:
  (b0 ⇒ (env,[x1],s) ---> ([word (x:word4)],s)) ⇒
  b0 ⇒ (env,[x1],s) ---> ([Num (w2n x)],s)
Proof
  fs [word_def]
QED

Theorem auto_word64_w2n:
  (b0 ⇒ (env,[x1],s) ---> ([word (x:word64)],s)) ⇒
  b0 ⇒ (env,[x1],s) ---> ([Num (w2n x)],s)
Proof
  fs [word_def]
QED

(* common definitions for custom datatypes *)

Definition case_lets_def[simp]:
  case_lets y [] x = x ∧
  case_lets y (v::vs) x = Let (name v) (Op Head [y]) (case_lets (Op Tail [y]) vs x)
End

Definition case_tree_def[simp]:
  case_tree y [] = Const 0 ∧
  case_tree y ((n,vars,x)::xs) =
    If Equal [Const (name n); Op Head [y]]
      (case_lets (Op Tail [y]) vars x)
      (case_tree (y:exp) xs)
End

Definition case_enum_def[simp]:
  case_enum y [] = Const 0 ∧
  case_enum y ((n,x)::xs) = If Equal [y; Const (name n)] x (case_enum (y:exp) xs)
End

(* a bit of automation for cons lemmas *)

local
  val b_tm = “b:bool”
  val x_tm = “x:exp”
  val v_tm = “v:v”
in
  val env_tm = “env:num -> v option”
  val basic_tm = “^b_tm ⇒ (^env_tm,[^x_tm],s) ---> ([^v_tm],s)”
  fun mk_basic_env env b x v =
    basic_tm |> subst [env_tm|->env,v_tm|->v,b_tm|->b,x_tm|->x]
  val mk_basic = mk_basic_env env_tm
end

fun prove_cons inv_def = let
  fun prove_cons th = let
    val x = th |> concl
    val body = repeat (snd o dest_forall) x
    val (l,r) = dest_eq body
    val (name,is_enum) = (r |> rand |> rator |> rand |> rand, false)
                         handle HOL_ERR _ => (r |> rand, true)
    val const = “Const ^name”
    val vs = if is_enum then [] else r |> rand |> rand |> listSyntax.dest_list |> fst
    fun mk v = let
      val vn = v |> rand |> dest_var |> fst
      val new_x = mk_var("x_" ^ vn, “:exp”)
      val new_b = mk_var("b_" ^ vn, “:bool”)
      in (new_b,(new_x,mk_basic new_b new_x v)) end
    val xs = map mk vs
    val exps = const :: (map (fst o snd) xs @ [“Const 0”])
    val bs = if null xs then T else list_mk_conj (map fst xs)
    val new_x = if is_enum then const
                else mk_comb(“parsing$conses”,listSyntax.mk_list(exps,type_of const))
    val goal = mk_basic bs new_x l
    val goal = if null xs then goal else
      mk_imp(list_mk_conj (map (snd o snd) xs),goal)
    val tac =
      rw [Eval_eq,th,return_def,name_def,AllCaseEqs(),PULL_EXISTS,fail_def,
          parsingTheory.conses_def,eval_op_def]
      \\ fs [] \\ rpt (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    val res = prove(goal,tac)
    in res |> PURE_REWRITE_RULE [parsingTheory.conses_def] end
  in inv_def |> CONJUNCTS |> map prove_cons |> LIST_CONJ end

(* a bit of automation for case lemmas *)

fun prove_case inv_def = let
  fun right_dest f z =
    (case f z of (x,y) => [x] @ right_dest f y) handle HOL_ERR _ => [z];
  val inv_rows = inv_def |> CONJUNCTS
  val ty = inv_rows |> hd |> SPEC_ALL |> concl |> dest_eq |> fst |> rand |> type_of
  val in_inv = inv_rows |> hd |> SPEC_ALL |> concl |> dest_eq |> fst |> rator
  val case_const = TypeBase.case_const_of ty
  val conses = TypeBase.constructors_of ty
  fun dest_fun_type ty =
    case dest_type ty of ("fun",[a,b]) => (a,b) | _ => fail()
  val tys = tl (right_dest dest_fun_type (type_of case_const))
  val res_ty = last tys
  val case_tys = butlast tys
  fun mk_funs (c,ty) = mk_var("f_" ^ fst (dest_const c), ty)
  val f_tms = map mk_funs (zip conses case_tys)
  val v = mk_var("v0",ty)
  val res = list_mk_comb(case_const, v :: f_tms)
  val inv = mk_var(dest_vartype res_ty |> explode |> tl |> implode,
               mk_type("fun",[res_ty,“:v”]))
  val res_v = mk_comb(inv,res)
  val b0 = mk_var("b0",“:bool”)
  val x0 = mk_var("x0",“:exp”)
  val v0 = mk_var("v0",ty)
  val asm0 = mk_basic b0 x0 (mk_comb(in_inv,v0))
(*
  val (f,c) = hd (zip f_tms conses)
*)
  fun process_row (f,c) = let
    val s = dest_const c |> fst
    val row = first (can (find_term (aconv c)) o concl) inv_rows |> SPEC_ALL
    val c_case = row |> concl |> rator |> rand |> rand
    val cs = row |> concl |> rand |> rand
    val (name,is_enum) = (cs |> rator |> rand |> rand,false) handle HOL_ERR _ => (cs,true)
    val args = if is_enum then [] else cs |> rand |> listSyntax.dest_list |> fst
    val vs = map rand args
    val res = list_mk_comb(f,vs)
    (* make the b *)
    val bvar = mk_var("b_" ^ s,
        wfrecUtils.list_mk_fun_type(map (type_of o rand) args @ [“:bool”]))
    val b_tm = list_mk_comb(bvar,vs)
    (* make env *)
    val strs = map (fn v => mk_var(fst (dest_var v) ^ "_" ^ s,“:string”)) vs
    val nums = map (fn t => “name ^t”) strs
    val ups = map combinSyntax.mk_update (zip nums (map optionSyntax.mk_some args))
    val new_env = foldl mk_comb env_tm ups
    (* make asm *)
    val x = mk_var(s ^ "_exp",“:exp”)
    val asm = list_mk_forall(vs,mk_basic_env new_env b_tm x (mk_comb(inv,res)))
    (* for code construction *)
    val t1 = name |> rand
    val t2 = listSyntax.mk_list(strs,“:string”)
    val t = if is_enum then pairSyntax.mk_pair(t1,x)
            else pairSyntax.mk_pair(t1,pairSyntax.mk_pair(t2,x))
    (* construct pre *)
    val ns = listSyntax.mk_list(if null nums then [] else butlast nums,“:num”)
    val b_tm = if is_enum then b_tm else
                 mk_conj(b_tm,“ALL_DISTINCT (^ns ++ free_vars ^x0)”)
    val pre = list_mk_forall(vs,mk_imp(mk_eq(v0,c_case),b_tm))
    in (asm,(t,pre)) end
  val xs = map process_row (zip f_tms conses)
  val asm = list_mk_conj(b0 :: map (snd o snd) xs)
  val ys = map (fst o snd) xs
  val x = listSyntax.mk_list(ys,type_of(hd ys))
  val is_enum = not (can (first (can dest_fun_type o type_of)) conses)
  val code = if is_enum then list_mk_comb(“case_enum”,[x0,x])
             else list_mk_comb(“case_tree”,[x0,x])
  val goal = mk_imp(list_mk_conj(asm0::map fst xs),mk_basic asm code res_v)
  val tac =
      Cases_on ‘v0’ \\ fs [] \\ rw [] \\ fs []
      \\ rpt (full_simp_tac (srw_ss())
                 [Eval_eq,PULL_EXISTS,eval_op_def,AllCaseEqs(),fail_def,
                  take_branch_def,return_def,name_def]
              \\ goal_assum (first_assum o mp_then Any mp_tac)
              \\ full_simp_tac (srw_ss()) [])
  in prove(goal,tac)
     |> PURE_REWRITE_RULE [case_lets_def,case_tree_def,case_enum_def] end

(* token *)

Definition token_def[simp]:
  token DOT = list [Name "DOT"] ∧
  token OPEN = list [Name "OPEN"] ∧
  token CLOSE = list [Name "CLOSE"] ∧
  token (NUM n) = list [Name "NUM"; Num n] ∧
  token (QUOTE n) = list [Name "QUOTE"; Num n]
End

Theorem auto_token_cons = prove_cons token_def;
Theorem auto_token_case = prove_case token_def;

(* test *)

Definition test_def[simp]:
  test source_syntax$Equal = Name "Equal" ∧
  test source_syntax$Less = Name "Less"
End

Theorem auto_test_cons = prove_cons test_def;
Theorem auto_test_case = prove_case test_def;

(* op *)

Definition op_def[simp]:
  op Add = Name "Add" ∧
  op Sub = Name "Sub" ∧
  op Div = Name "Div" ∧
  op Cons = Name "Cons" ∧
  op Head = Name "Head" ∧
  op Tail = Name "Tail" ∧
  op Read = Name "Read" ∧
  op Write = Name "Write"
End

Theorem auto_op_cons = prove_cons op_def;
Theorem auto_op_case = prove_case op_def;

(* app_list *)

Definition app_list_def[simp]:
  app_list a (List xs) = list [Name "List"; list a xs] ∧
  app_list a (Append x y) = list [Name "Append"; app_list a x; app_list a y]
End

Theorem auto_app_list_cons = prove_cons app_list_def;
Theorem auto_app_list_case = prove_case app_list_def;

(* exp *)

Definition exp_def:
  exp (Const n) = list [Name "Const"; Num n] ∧
  exp (Var n) = list [Name "Var"; Num n] ∧
  exp (Op f xs) = list [Name "Op"; op f; list (MAP exp xs)] ∧
  exp (If t xs e1 e2) = list [Name "If"; test t; list (MAP exp xs); exp e1; exp e2] ∧
  exp (Let n e1 e2) = list [Name "Let"; Num n; exp e1; exp e2] ∧
  exp (Call n xs) = list [Name "Call"; Num n; list (MAP exp xs)]
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ qsuff_tac ‘∀xs a. MEM a xs ⇒ exp_size a < exp1_size xs’
  \\ TRY (rw []  \\ res_tac \\ fs [] \\ NO_TAC)
  \\ Induct \\ fs [exp_size_def]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
End

Theorem exp_def[simp,allow_rebind] =
        exp_def |> REWRITE_RULE [GSYM map_def]
                |> CONV_RULE (DEPTH_CONV ETA_CONV);

Theorem auto_exp_cons = prove_cons exp_def;
Theorem auto_exp_case = prove_case exp_def;

(* dec *)

Definition dec_def[simp]:
  dec (Defun n ns x) = list [Name "Defun"; Num n; list Num ns; exp x]
End

Theorem auto_dec_cons = prove_cons dec_def;
Theorem auto_dec_case = prove_case dec_def;

(* prog *)

Definition prog_def[simp]:
  prog (Program ds x) = list [Name "Program"; list dec ds; exp x]
End

Theorem auto_prog_cons = prove_cons prog_def;
Theorem auto_prog_case = prove_case prog_def;

(* reg *)

Definition reg_def[simp]:
  reg RAX = Name "RAX" ∧
  reg RDI = Name "RDI" ∧
  reg RBX = Name "RBX" ∧
  reg RBP = Name "RBP" ∧
  reg R12 = Name "R12" ∧
  reg R13 = Name "R13" ∧
  reg R14 = Name "R14" ∧
  reg R15 = Name "R15" ∧
  reg RDX = Name "RDX"
End

Theorem auto_reg_cons = prove_cons reg_def;
Theorem auto_reg_case = prove_case reg_def;

(* cond *)

Definition cond_def[simp]:
  cond Always = list [Name "Always"] ∧
  cond (Less r1 r2) = list [Name "Less"; reg r1; reg r2] ∧
  cond (Equal r1 r2) = list [Name "Equal"; reg r1; reg r2]
End

Theorem auto_cond_cons = prove_cons cond_def;
Theorem auto_cond_case = prove_case cond_def;

(* inst *)

Definition inst_def[simp]:
  inst (Const r1 w64)  = list [Name "Const"; reg r1; word w64] ∧
  inst (Mov r1 r2)     = list [Name "Mov"; reg r1; reg r2] ∧
  inst (Add r1 r2)     = list [Name "Add"; reg r1; reg r2] ∧
  inst (Sub r1 r2)     = list [Name "Sub"; reg r1; reg r2] ∧
  inst (Div r1)        = list [Name "Div"; reg r1] ∧
  inst (Jump c n)      = list [Name "Jump"; cond c; Num n] ∧
  inst (Call n)        = list [Name "Call"; Num n] ∧
  inst (Ret)           = list [Name "Ret"] ∧
  inst (Pop r1)        = list [Name "Pop"; reg r1] ∧
  inst (Push r1)       = list [Name "Push"; reg r1] ∧
  inst (Add_RSP n)     = list [Name "Add_RSP"; Num n] ∧
  inst (Load_RSP r n)  = list [Name "Load_RSP"; reg r; Num n] ∧
  inst (Load r1 r2 i)  = list [Name "Load"; reg r1; reg r2; word i] ∧
  inst (Store r1 r2 i) = list [Name "Store"; reg r1; reg r2; word i] ∧
  inst (GetChar)       = list [Name "GetChar"] ∧
  inst (PutChar)       = list [Name "PutChar"] ∧
  inst (Exit)          = list [Name "Exit"] ∧
  inst (Comment s)     = list [Name "Comment"; list char s]
End

Theorem auto_inst_cons = prove_cons inst_def;
Theorem auto_inst_case = prove_case inst_def;

(* optimizer *)

Theorem inline_let: (* inline any let where the bound name doesn't fit 2**64 *)
  (b ⇒ (env,[x],s) ---> ([v],s)) ⇒
  LFINITE s.input ⇒
  (b ⇒ (env,[inline_let (λn. 18446744073709551616 ≤ n) x],s) ---> ([v],s))
Proof
  rw [] \\ match_mp_tac (MP_CANON inline_let_thm) \\ fs []
QED

val _ = export_theory();
