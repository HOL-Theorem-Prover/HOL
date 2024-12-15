
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory source_semanticsTheory mp_then
     source_propertiesTheory parsingTheory codegenTheory x64asm_syntaxTheory
     wordsTheory wordsLib automation_lemmasTheory automationLib;

val _ = new_theory "compiler_prog";

val _ = show_assums := true;

val _ = attach_comment ‘
# This file is generated from the HOL4 theorem prover.

# The code in this file implements a verified bootstrapped compiler
# for a small Lisp-inspired language. The compiler consists of:
#
#  - a code generator (codegen)
#  - a lexer and a parser
#  - a printer that outputs GNU assmebler for Ubuntu x86-64
#
# Lines beginning with # are comments.


# Definition of the codegen function’

val _ = temp_delsimps ["LT1_EQ0"]

(* codegen *)

val res = to_deep APPEND;
val res = to_deep codegenTheory.flatten_def;
val res = to_deep (init_def |> SIMP_RULE std_ss [])
val res = to_deep even_len_def

Theorem even_len_side:
  ∀v. (even_len_side v = T) ∧ (odd_len_side v = T)
Proof
  Induct \\ fs [] \\ ntac 2 (once_rewrite_tac [res] \\ fs []) \\ EVAL_TAC
QED

val _ = update_mem even_len_side;

val res = to_deep give_up_def
val res = to_deep (c_const_def |> REWRITE_RULE [EVAL “2 ** 63 − 1n”])

Theorem c_const_side:
  c_const_side l n vs = T
Proof
  fs [] \\ once_rewrite_tac [res] \\ CCONTR_TAC \\ fs []
QED

val _ = update_mem c_const_side;

val res = to_deep find_def
val res = to_deep c_var_def
val res = to_deep c_add_def
val res = to_deep c_sub_def
val res = to_deep c_div_def
val res = to_deep c_cons_def
val res = to_deep c_head_def
val res = to_deep c_tail_def
val res = to_deep align_def
val res = to_deep c_read_def
val res = to_deep c_write_def
val res = to_deep c_op_def
val res = to_deep c_test_def

Theorem c_if_thm:
  c_if t cmp x1 x2 x3 =
    (Append (FST x1)
      (Append (List (c_test cmp (SND x2 + if t then 0 else 1)))
        (Append (FST x2)
          (Append (List (if t then [] else [Jump Always (SND x3)])) (FST x3)))),
          SND x3)
Proof
  PairCases_on ‘x1’ \\ PairCases_on ‘x2’ \\ PairCases_on ‘x3’ \\ fs [c_if_def]
QED

val res = to_deep c_if_thm
val res = to_deep (LENGTH |> REWRITE_RULE [ADD1])
val res = to_deep call_env_def
val res = to_deep c_pushes_def
val res = to_deep c_pops_def
val res = to_deep c_call_def
val res = to_deep codegenTheory.lookup_def
val res = to_deep make_ret_def
val res = to_deep c_exp_def

Triviality FST_SND:
  FST = (λ(x,y). x) ∧ SND = (λ(x,y). y)
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem c_exp_side:
  (∀t l vs fs z. c_exp_side t l vs fs z = T) ∧
  (∀l vs fs zs. c_exps_side l vs fs zs = T)
Proof
  ho_match_mp_tac c_exp_ind_alt \\ rw []
  \\ once_rewrite_tac [res] \\ fs [FST_SND]
  \\ rpt (pairarg_tac \\ fs []) \\ rw [] \\ fs [name_def]
QED

val _ = update_mem c_exp_side;

Theorem c_defun_thm:
  c_defun l fs (Defun n vs body) =
    let r1 = c_pushes vs l in
    let r2 = c_exp T (SND (SND r1)) (FST (SND r1)) fs body in
      (Append (FST r1) (FST r2), SND r2)
Proof
  fs [c_defun_def] \\ rpt (pairarg_tac \\ fs [])
QED

val res = to_deep c_defun_thm
val res = to_deep name_of_def

Definition mul256_def:
  mul256 n =
    let n = n + n in
    let n = n + n in
    let n = n + n in
    let n = n + n in
    let n = n + n in
    let n = n + n in
    let n = n + n in
            n + n : num
End

val res = to_deep mul256_def;

Theorem mul256_thm[simp]:
  mul256_side n ∧
  mul256 n = 256 * n
Proof
  fs [mul256_def,res]
QED

Theorem name2str_thm:
  name2str n acc =
    if n = 0 then acc else
      let d = n DIV 256 in
      let m = n - mul256 d in
        name2str d (STRING (CHR m) acc)
Proof
  simp [Once codegenTheory.name2str_def]
  \\ rw [] \\ ‘0 < 256n’ by fs []
  \\ drule DIVISION
  \\ disch_then (qspec_then ‘n’ strip_assume_tac)
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ decide_tac
QED

Definition name2str_temp:
  name2str_temp n acc =
    if n = 0 then acc else
      let d = n DIV 256 in
      let m = n - mul256 d in
        name2str_temp d (STRING (CHR m) acc)
End

Theorem name2str_ind = name2str_temp_ind

val res = to_deep name2str_thm

Triviality name2str_side:
  ∀n acc. name2str_side n acc ⇔ T
Proof
  completeInduct_on ‘n’ \\ fs []
  \\ once_rewrite_tac [res]
  \\ Cases_on ‘n = 0’ \\ fs []
  \\ rw [] \\ ‘0 < 256n’ by fs []
  \\ drule DIVISION
  \\ disch_then (qspec_then ‘n’ strip_assume_tac)
  \\ decide_tac
QED

val _ = update_mem name2str_side;

val res = to_deep c_decs_def;

Theorem codegen_thm:
  codegen (Program decs main) =
    let r1 = c_decs 17 [] decs in
    let r2 = c_decs 17 (FST (SND r1)) (decs ++ [Defun (name "main") [] main]) in
      flatten (Append (List (init (SND (SND r1) + 1))) (FST r2)) []
Proof
  fs [codegen_def,EVAL “LENGTH (init 0)”] \\ rpt (pairarg_tac \\ fs [])
QED

val res = to_deep (codegen_thm |> SIMP_RULE (srw_ss()) [name_def]);


(* lexer *)

val _ = attach_comment ‘

# Definition of the lexer that reads from stdin’

Definition mul10_def:
  mul10 n =
    let n2 = n + n in
    let n4 = n2 + n2 in
    let n5 = n4 + n in
      n5 + n5 : num
End

val res = to_deep mul10_def;

Theorem mul10_thm[simp]:
  mul10_side n ∧
  mul10 n = 10 * n
Proof
  fs [mul10_def,res]
QED

val read_num_code_def = define_code ‘
  (defun read_num (acc next)
     (if (< next '58)
       (if (< next '48)
         (cons acc next)
         (read_num
           (+ (mul10 acc) (- next '48))
           (read)))
       (cons acc next)))’

val read_str_code_def = define_code ‘
  (defun read_str (acc next)
     (if (< next '123)
       (if (< next '42)
         (cons acc next)
         (read_str
           (+ (mul256 acc) next)
           (read)))
       (cons acc next)))’

val read_any_code_def = define_code ‘
  (defun read_any (next)
     (if (< next '58)
       (if (< next '48)
         (read_str '0 next)
         (read_num '0 next))
       (read_str '0 next)))’

Theorem read_num_thm:
  ∀input s acc k rest.
    read_num #"0" #"9" 10 (ORD #"0") acc input = (k, rest) ∧
    lookup_fun (name "mul10") s.funs = SOME ([name "n"],mul10_code) ∧
    lookup_fun (name "read_num") s.funs = SOME ([name "acc"; name "next"],read_num_code) ∧
    s.input = fromList (TL input) ⇒
    app (name "read_num") [Num acc; next (fromList input)] s
      (Pair (Num k) (next (fromList rest)), s with input := fromList (TL rest))
Proof
  gen_tac \\ completeInduct_on ‘LENGTH input’
  \\ rw [] \\ fs [PULL_FORALL]
  \\ match_mp_tac (trans_app |> SIMP_RULE std_ss [LET_THM] |> MP_CANON |> GEN_ALL)
  \\ fs [make_env_def]
  \\ simp [read_num_code_def]
  \\ simp [Eval_eq,PULL_EXISTS]
  \\ fs [combinTheory.APPLY_UPDATE_THM,name_def]
  \\ Cases_on ‘input’ \\ fs [next_def]
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 fs [state_component_equality]
  \\ reverse IF_CASES_TAC
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 (rw [] \\ fs [state_component_equality,next_def])
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  \\ IF_CASES_TAC
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 (rw [] \\ fs [state_component_equality,next_def])
  \\ (theorem "mul10_app" |> DISCH_ALL |> Q.INST [‘n’|->‘acc’]
         |> SIMP_RULE (srw_ss()) [] |> mp_tac)
  \\ fs [name_def,llistTheory.LFINITE_fromList]
  \\ strip_tac \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [] \\ Cases_on ‘t’ \\ fs [AND_IMP_INTRO]
  \\ first_x_assum (first_assum o mp_then (Pos (el 2)) mp_tac)
  \\ fs []
  THEN1 (disch_then (qspec_then ‘s with input := fromList ""’ mp_tac) \\ fs [])
  \\ disch_then (qspec_then ‘s with input := fromList t'’ mp_tac) \\ fs []
QED

Theorem read_str_thm:
  ∀input s acc k rest.
    read_num #"*" #"z" 256 0 acc input = (k, rest) ∧
    lookup_fun (name "mul256") s.funs = SOME ([name "n"],mul256_code) ∧
    lookup_fun (name "read_str") s.funs = SOME ([name "acc"; name "next"],read_str_code) ∧
    s.input = fromList (TL input) ⇒
    app (name "read_str") [Num acc; next (fromList input)] s
      (Pair (Num k) (next (fromList rest)), s with input := fromList (TL rest))
Proof
  gen_tac \\ completeInduct_on ‘LENGTH input’
  \\ rw [] \\ fs [PULL_FORALL]
  \\ match_mp_tac (trans_app |> SIMP_RULE std_ss [LET_THM] |> MP_CANON |> GEN_ALL)
  \\ fs [make_env_def]
  \\ simp [read_str_code_def]
  \\ simp [Eval_eq,PULL_EXISTS]
  \\ fs [combinTheory.APPLY_UPDATE_THM,name_def]
  \\ Cases_on ‘input’ \\ fs [next_def]
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 fs [state_component_equality]
  \\ reverse IF_CASES_TAC
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 (rw [] \\ fs [state_component_equality,next_def])
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  \\ IF_CASES_TAC
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 (rw [] \\ fs [state_component_equality,next_def])
  \\ (theorem "mul256_app" |> DISCH_ALL |> Q.INST [‘n’|->‘acc’]
         |> SIMP_RULE (srw_ss()) [] |> mp_tac)
  \\ fs [name_def,llistTheory.LFINITE_fromList]
  \\ strip_tac \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [] \\ Cases_on ‘t’ \\ fs [AND_IMP_INTRO]
  \\ first_x_assum (first_assum o mp_then (Pos (el 2)) mp_tac)
  \\ fs []
  THEN1 (disch_then (qspec_then ‘s with input := fromList ""’ mp_tac) \\ fs [])
  \\ disch_then (qspec_then ‘s with input := fromList t'’ mp_tac) \\ fs []
QED

val end_line_code_def = define_code ‘
  (defun end_line (next)
     (if (< next '256)
       (if (= next '10) (read) (end_line (read)))
       next))’

Theorem end_line_thm:
  ∀input s.
    lookup_fun (name "end_line") s.funs = SOME ([name "next"],end_line_code) ∧
    s.input = fromList (TL input) ⇒
    app (name "end_line") [next (fromList input)] s
      (next (fromList (end_line input)), s with input := fromList (TL (end_line input)))
Proof
  simp [] \\ gen_tac \\ completeInduct_on ‘LENGTH input’
  \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ match_mp_tac (trans_app |> SIMP_RULE std_ss [LET_THM] |> MP_CANON |> GEN_ALL)
  \\ fs [make_env_def]
  \\ simp [end_line_code_def]
  \\ simp [Eval_eq,PULL_EXISTS]
  \\ fs [combinTheory.APPLY_UPDATE_THM,name_def]
  \\ Cases_on ‘input’ \\ fs [next_def]
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 fs [state_component_equality,lex_def,end_line_def,next_def]
  \\ fs [ORD_BOUND]
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  \\ fs [end_line_def]
  \\ Cases_on ‘h’ \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ simp [Eval_eq,PULL_EXISTS]
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  \\ fs [AND_IMP_INTRO,state_component_equality]
  THEN1 (Cases_on ‘t’ \\ fs [])
  \\ first_x_assum (qspecl_then [‘t’,‘s with input := fromList (TL t)’] mp_tac) \\ fs []
  \\ Cases_on ‘t’ \\ fs []
QED

val lex_code_def = define_code ‘
  (defun lex (q next acc)
     (if (< next '* )
       (let (n (read))
         (if (= next '40) (lex '0 n (cons (OPEN) acc))
           (if (= next '41) (lex '0 n (cons (CLOSE) acc))
             (if (= next '39) (lex '1 n acc)
               (if (= next '35) (lex '0 (end_line n) acc)
                 (lex '0 n acc))))))
       (if (= next '46)
         (lex '0 (read) (cons (DOT) acc))
         (if (< 'z next)
           (if (< next '256)
             (lex '0 (read) acc) acc)
             (let (r (read_any next))
               (lex '0 (tail r)
                 (if (= q '0)
                   (cons (NUM (head r)) acc)
                   (cons (QUOTE (head r)) acc))))))))’

val lexer_code_def = define_code ‘
  (defun lexer ()
     (lex '0 (read) '0))’

Triviality LTL_fromList_lemma[simp]:
  (case LTL (fromList t) of NONE => fromList t | SOME t => t) = fromList (TL t)
Proof
  Cases_on ‘t’ \\ fs []
QED

Theorem lex_thm:
  ∀input s acc k toks.
    lookup_fun (name "mul10") s.funs = SOME ([name "n"],mul10_code) ∧
    lookup_fun (name "mul256") s.funs = SOME ([name "n"],mul256_code) ∧
    lookup_fun (name "end_line") s.funs = SOME ([name "next"],end_line_code) ∧
    lookup_fun (name "read_num") s.funs = SOME ([name "acc"; name "next"],read_num_code) ∧
    lookup_fun (name "read_str") s.funs = SOME ([name "acc"; name "next"],read_str_code) ∧
    lookup_fun (name "read_any") s.funs = SOME ([name "next"],read_any_code) ∧
    lookup_fun (name "lex") s.funs = SOME ([name "q"; name "next"; name "acc"],lex_code) ∧
    s.input = fromList (TL input) ∧
    lex (if k = 0 then NUM else QUOTE) input acc = toks ⇒
    app (name "lex") [Num k; next (fromList input); list token acc] s
      (list token toks, s with input := fromList [])
Proof
  simp [] \\ gen_tac \\ completeInduct_on ‘LENGTH input’
  \\ rw [] \\ fs [PULL_FORALL]
  \\ match_mp_tac (trans_app |> SIMP_RULE std_ss [LET_THM] |> MP_CANON |> GEN_ALL)
  \\ fs [make_env_def]
  \\ simp_tac std_ss [Once lex_code_def]
  \\ simp_tac (srw_ss()) [Once Eval_eq,PULL_EXISTS]
  \\ fs [combinTheory.APPLY_UPDATE_THM,name_def]
  \\ Cases_on ‘input’ \\ fs [next_def]
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1 fs [state_component_equality,lex_def]
  \\ IF_CASES_TAC
  \\ rpt BasicProvers.var_eq_tac
  \\ fs [take_branch_def,return_def,Eval_eq,PULL_EXISTS,next_def,
         combinTheory.APPLY_UPDATE_THM,eval_op_def,read_num_def]
  THEN1
   (IF_CASES_TAC
    \\ fs [Eval_eq,PULL_EXISTS,combinTheory.APPLY_UPDATE_THM,eval_op_def,return_def]
    THEN1
     (Cases_on ‘h’ \\ fs [lex_def] \\ rw [] \\ fs [AND_IMP_INTRO]
      \\ first_x_assum (qspecl_then [‘t’,
           ‘s with input := fromList (TL t)’,‘OPEN::acc’,‘0’] mp_tac)
      \\ fs [name_def])
    \\ fs [Eval_eq,eval_op_def,return_def, take_branch_def]
    \\ IF_CASES_TAC
    THEN1
     (Cases_on ‘h’ \\ fs [lex_def] \\ rw []
      \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
             eval_op_def,return_def]
      \\ first_x_assum (qspecl_then [‘t’,
           ‘s with input := fromList (TL t)’,‘CLOSE::acc’,‘0’] mp_tac)
      \\ fs [name_def])
    \\ fs [Eval_eq,eval_op_def,return_def, take_branch_def,PULL_EXISTS,
           combinTheory.APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    THEN1
     (Cases_on ‘h’ \\ fs [lex_def] \\ rw []
      \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
             eval_op_def,return_def]
      \\ first_x_assum (qspecl_then [‘t’,
           ‘s with input := fromList (TL t)’,‘acc’,‘1’] mp_tac)
      \\ fs [name_def])
    \\ fs [Eval_eq,eval_op_def,return_def, take_branch_def,PULL_EXISTS,
           combinTheory.APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    THEN1
     (Cases_on ‘h’ \\ fs [lex_def] \\ rw []
      \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
             eval_op_def,return_def]
      \\ qspecl_then [‘t’,‘s with input := fromList (TL t)’] mp_tac
           (SIMP_RULE (srw_ss()) [name_def] end_line_thm)
      \\ fs [next_def]
      \\ strip_tac \\ goal_assum (first_assum o mp_then Any mp_tac)
      \\ first_x_assum (qspecl_then [‘end_line t’,
            ‘s with input := fromList (TL (end_line t))’,‘acc’,‘0’] mp_tac)
      \\ fs [name_def]
      \\ disch_then match_mp_tac \\ fs [end_line_length])
    \\ fs [Eval_eq,eval_op_def,return_def, take_branch_def,PULL_EXISTS,
           combinTheory.APPLY_UPDATE_THM]
    \\ Cases_on ‘h’ \\ fs [lex_def] \\ rw [] \\ fs []
    \\ first_x_assum (qspecl_then [‘t’,‘s with input := fromList (TL t)’,‘acc’,‘0’]
                      mp_tac) \\ fs [name_def]
    \\ fs [read_num_def])
  \\ IF_CASES_TAC
  THEN1
   (Cases_on ‘h’ \\ fs [lex_def] \\ rw []
    \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
           eval_op_def,return_def]
    \\ first_x_assum (qspecl_then [‘t’,‘s with input := fromList (TL t)’,‘DOT::acc’,‘0’]
                      mp_tac) \\ fs [name_def,next_def])
  \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
         eval_op_def,return_def,take_branch_def]
  \\ IF_CASES_TAC
  THEN1
   (fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
        eval_op_def,return_def,take_branch_def,ORD_BOUND]
    \\ first_x_assum (qspecl_then [‘t’,‘s with input := fromList (TL t)’,‘acc’,‘0’]
                      mp_tac) \\ fs [name_def,lex_def]
    \\ rw [] \\ fs [read_num_def,next_def])
  \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
         eval_op_def,return_def,take_branch_def,ORD_BOUND]
  \\ fs [lex_def]
  \\ qpat_abbrev_tac ‘pp2 = if k = 0 then _ else _’
  \\ qpat_abbrev_tac ‘pp = if k = 0 then _ else _’
  \\ rw [] \\ fs []
  \\ simp [Once app_cases,PULL_EXISTS,env_and_body_def,make_env_def]
  \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,name_def,
         eval_op_def,return_def,take_branch_def,read_any_code_def]
  \\ reverse (Cases_on ‘ORD #"0" ≤ ORD h ⇒ ORD #"9" < ORD h’) \\ fs [NOT_LESS]
  THEN1
   (fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,name_def,
        eval_op_def,return_def,take_branch_def,read_any_code_def]
    \\ pairarg_tac \\ fs []
    \\ drule (read_num_thm |> SIMP_RULE (srw_ss()) []) \\ fs [next_def]
    \\ disch_then (qspec_then ‘s’ mp_tac) \\ fs [name_def]
    \\ strip_tac \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [] \\ reverse IF_CASES_TAC
    THEN1
     (fs [] \\ rfs [read_num_def]
      \\ imp_res_tac read_num_length \\ fs [])
    \\ unabbrev_all_tac \\ fs []
    \\ Cases_on ‘k = 0’ \\ fs []
    \\ fs [PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,name_def,
           eval_op_def,return_def,take_branch_def]
    \\ imp_res_tac read_num_length \\ fs []
    \\ first_x_assum (qspecl_then [‘rest’,‘s with input := fromList (TL rest)’,
         ‘if k = 0 then NUM n::acc else QUOTE n::acc’,‘0’] mp_tac)
    \\ fs [name_def])
  \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
         eval_op_def,return_def,take_branch_def,read_any_code_def,name_def]
  \\ IF_CASES_TAC
  \\ pairarg_tac \\ fs []
  \\ pop_assum (mp_tac o REWRITE_RULE [read_num_def]) \\ fs []
  \\ rw []
  \\ fs [AND_IMP_INTRO,PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,
         eval_op_def,return_def,take_branch_def,name_def]
  \\ pairarg_tac \\ fs []
  \\ drule (read_str_thm |> SIMP_RULE (srw_ss()) []) \\ fs [next_def,name_def]
  \\ disch_then (qspec_then ‘s’ mp_tac) \\ fs [name_def]
  \\ strip_tac \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [] \\ (reverse IF_CASES_TAC
  THEN1 (fs [] \\ rfs [read_num_def] \\ imp_res_tac read_num_length \\ fs []))
  \\ ‘rest' ≠ STRING h t’ by fs [read_num_def]
  \\ unabbrev_all_tac \\ fs []
  \\ Cases_on ‘k = 0’ \\ fs []
  \\ fs [PULL_EXISTS,Eval_eq,combinTheory.APPLY_UPDATE_THM,name_def,
         eval_op_def,return_def,take_branch_def]
  \\ imp_res_tac read_num_length \\ fs []
  \\ first_x_assum (qspecl_then [‘rest'’,
       ‘s with input := fromList (TL rest')’,
       ‘if k = 0 then NUM n' :: acc else QUOTE n'::acc’,‘0’] mp_tac)
  \\ fs [name_def] \\ rfs []
QED

Theorem lexer_thm:
  lookup_fun (name "mul10") s.funs = SOME ([name "n"],mul10_code) ∧
  lookup_fun (name "mul256") s.funs = SOME ([name "n"],mul256_code) ∧
  lookup_fun (name "end_line") s.funs = SOME ([name "next"],end_line_code) ∧
  lookup_fun (name "read_num") s.funs = SOME ([name "acc"; name "next"],read_num_code) ∧
  lookup_fun (name "read_str") s.funs = SOME ([name "acc"; name "next"],read_str_code) ∧
  lookup_fun (name "read_any") s.funs = SOME ([name "next"],read_any_code) ∧
  lookup_fun (name "lex") s.funs = SOME ([name "q"; name "next"; name "acc"],lex_code) ∧
  lookup_fun (name "lexer") s.funs = SOME ([],lexer_code) ∧
  s.input = fromList input ⇒
  app (name "lexer") [] s (list token (lexer input), s with input := LNIL)
Proof
  rw []
  \\ match_mp_tac (trans_app |> SIMP_RULE std_ss [LET_THM] |> MP_CANON |> GEN_ALL)
  \\ fs [make_env_def]
  \\ simp [lexer_code_def]
  \\ simp [Eval_eq,PULL_EXISTS,eval_op_def,return_def]
  \\ qspecl_then [‘input’,‘s with input := fromList (TL input)’,‘[]’,‘0’]
       mp_tac (lex_thm |> SIMP_RULE std_ss [])
  \\ fs [lexer_def]
QED

(* parser *)

val _ = attach_comment ‘

# Definition of the parser’

val res = to_deep (quote_def |> SIMP_RULE (srw_ss()) [name_def]);
val res = to_deep (parse_def |> DefnBase.one_line_ify NONE |> Q.INST [‘v’|->‘input’]);

Theorem parse_side:
  ∀v x s. parse_side v x s = T
Proof
  Induct \\ fs [] \\ once_rewrite_tac [res] \\ fs []
QED

val _ = update_mem parse_side;

val res = to_deep v2list_def;
val res = to_deep parsingTheory.conses_def;
val res = to_deep (v2test_def |> SIMP_RULE (srw_ss()) [name_def]);

val h_code_def = define_code ‘
  (defun h (x) (if (= (head x) '1) x (head (tail x))))’

val t_code_def = define_code ‘
  (defun t (x) (if (= (head x) '1) x (tail (tail x))))’

val res = to_deep el1_def;
val res = to_deep el2_def;
val res = to_deep el3_def;
val res = to_deep vs2args_def;
val res = to_deep is_upper_def;
val res = to_deep pat_lets_def;
val res = to_deep num2exp_def;
val res = to_deep (v2exp_def |> CONV_RULE (apply_at_pat_conv “name _” EVAL));

Theorem v2exp_side:
  (∀v. v2exp_side v = T) ∧
  (∀v. v2exps_side v = T) ∧
  (∀v. v2lets_side v = T) ∧
  (∀v w. v2case_side v w = T)
Proof
  ho_match_mp_tac v2exp_ind
  \\ rpt strip_tac \\ simp []
  \\ once_rewrite_tac [res]
  \\ rpt (pop_assum mp_tac)
  \\ rpt (qpat_abbrev_tac ‘pat = name _’
          \\ pop_assum mp_tac
          \\ CONV_TAC (PATH_CONV "lrr" EVAL)
          \\ strip_tac \\ unabbrev_all_tac)
  \\ metis_tac []
QED

val _ = update_mem v2exp_side;

val res = to_deep v2dec_def;

Theorem vs2prog_thm:
  vs2prog vs =
    case vs of
    | [] => Program [] (Const 0)
    | (v::vs) =>
      case vs of
      | [] => Program [] (v2exp v)
      | (x::xs) => let p = vs2prog vs in
                     case p of Program ds m => Program (v2dec v :: ds) m
Proof
  fs [Once (DefnBase.one_line_ify NONE vs2prog_def)]
  \\ BasicProvers.every_case_tac \\ fs []
QED

val res = to_deep vs2prog_thm;
val res = to_deep parser_def;

(* asm2str *)

val _ = attach_comment ‘

# Functions for converting assembly to strings’

val res = to_deep x64asm_syntaxTheory.reg_def;

Theorem num_thm: (* this rephrasing avoids MOD, which is not supported *)
  num n s =
    if n < 10 then (CHR (48 + n))::s else
      let d = n DIV 10 in
      let m = n - mul10 d in
        num d ((CHR (48 + m)) :: s)
Proof
  simp [Once x64asm_syntaxTheory.num_def]
  \\ rw [] \\ ‘0 < 10n’ by fs []
  \\ drule DIVISION
  \\ disch_then (qspec_then ‘n’ strip_assume_tac)
  \\ AP_TERM_TAC \\ AP_THM_TAC \\ rpt AP_TERM_TAC \\ decide_tac
QED

Definition num_temp:
  num_temp n s =
    if n < 10 then (CHR (48 + n))::s else
      let d = n DIV 10 in
      let m = n - mul10 d in
        num_temp d ((CHR (48 + m)) :: s)
End

Theorem num_ind = num_temp_ind

val res = to_deep num_thm

Triviality num_side:
  ∀n s. num_side n s ⇔ T
Proof
  completeInduct_on ‘n’ \\ fs []
  \\ once_rewrite_tac [res]
  \\ Cases_on ‘n < 10’ \\ fs []
  \\ rw [] \\ ‘0 < 10n’ by fs []
  \\ drule DIVISION
  \\ disch_then (qspec_then ‘n’ strip_assume_tac)
  \\ decide_tac
QED

val _ = update_mem num_side;

val res = to_deep lab_def
val res = to_deep x64asm_syntaxTheory.clean_def

Definition mul8_def:
  mul8 n =
    let n = n + n in
    let n = n + n in
      n + n : num
End

val res = to_deep mul8_def;

Theorem mul8_thm[simp]:
  mul8_side n = T ∧
  mul8 n = 8 * n
Proof
  fs [mul8_def,res]
QED

val res = to_deep (x64asm_syntaxTheory.inst_def |> REWRITE_RULE [GSYM mul8_thm])
val res = to_deep x64asm_syntaxTheory.insts_def
val lemma = asm2str_def |> concl |> find_term (can (match_term “FLAT _”)) |> EVAL
val res = to_deep (asm2str_def |> SIMP_RULE std_ss [lemma])

(* print *)

val _ = attach_comment ‘

# A function for printing a list of characters to stdout’

val print_code_def = define_code ‘
  (defun print (s)
     (if (= s '0) '0
       (let
         (a (write (head s)))
         (print (tail s)))))’

Theorem print_thm:
  ∀str s.
    lookup_fun (name "print") s.funs = SOME ([name "s"],print_code) ⇒
    app (name "print") [list char str] s
      (Num 0, s with output := s.output ++ str)
Proof
  gen_tac \\ completeInduct_on ‘LENGTH str’
  \\ rw [] \\ fs [PULL_FORALL]
  \\ match_mp_tac (trans_app |> SIMP_RULE std_ss [LET_THM] |> MP_CANON |> GEN_ALL)
  \\ fs [make_env_def]
  \\ simp [print_code_def]
  \\ simp [Eval_eq,PULL_EXISTS]
  \\ fs [combinTheory.APPLY_UPDATE_THM]
  \\ rename [‘list (MAP char t)’]
  \\ Cases_on ‘t’ \\ fs []
  \\ fs [list_def,take_branch_def,return_def]
  \\ simp [Eval_eq,PULL_EXISTS]
  THEN1 fs [state_component_equality]
  \\ fs [combinTheory.APPLY_UPDATE_THM,eval_op_def,return_def,ORD_BOUND]
  \\ fs [name_def,AND_IMP_INTRO,CHR_ORD]
  \\ first_x_assum (qspecl_then [‘t'’,
      ‘s with output := STRCAT s.output (STRING h "")’] mp_tac)
  \\ fs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
QED

(* definition of whole program *)

val _ = attach_comment ‘

# The main expression’

local
val _ = max_print_depth := 15;
val main_exp = parse_exp ‘(print (asm2str (codegen (parser (lexer)))))’;
val entire_program = get_program main_exp;
in

Definition compiler_prog_def:
  compiler_prog = ^entire_program :prog
End

Triviality compiler_prog_thm = compiler_prog_def |> CONV_RULE (RAND_CONV EVAL);

Definition coms_def:
  coms = ^(get_comments ())
End

end

(* proving that it's correct *)

Theorem compiler_prog_correct:
  (input, compiler_prog) prog_terminates (compiler input)
Proof
  fs [prog_terminates_def,compiler_prog_thm,compiler_def]
  \\ qpat_abbrev_tac ‘pat = Defun _ _ _ :: _’
  \\ simp [Eval_eq,PULL_EXISTS]
  \\ qspecl_then [‘init_state (fromList input) pat’,‘input’]
       mp_tac (GEN_ALL lexer_thm)
  \\ impl_tac THEN1
    (rewrite_tac [read_num_code_def,read_str_code_def,read_any_code_def,
                  lex_code_def,lexer_code_def,end_line_code_def]
     \\ rpt strip_tac \\ unabbrev_all_tac \\ EVAL_TAC)
  \\ simp [name_def] \\ strip_tac
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ ‘init_state (fromList input) pat with input := LNIL = init_state LNIL pat’ by
      simp [init_state_def]
  \\ simp [] \\ pop_assum kall_tac
  \\ ‘∀input. (init_state input pat).input = input’ by (EVAL_TAC \\ fs [])
  \\ simp [] \\ pop_assum kall_tac
  \\ mp_tac (fetch "-" "parser_app" |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
      |> Q.INST [‘tokens’|->‘lexer input’,‘s’|->‘init_state LNIL pat’])
  \\ impl_tac THEN1 (unabbrev_all_tac \\ EVAL_TAC \\ fs [llistTheory.LFINITE_THM])
  \\ simp [name_def] \\ strip_tac
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ mp_tac (fetch "-" "codegen_app" |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
      |> Q.INST [‘v’|->‘parser (lexer input)’,‘s’|->‘init_state LNIL pat’])
  \\ impl_tac THEN1 (unabbrev_all_tac \\ EVAL_TAC \\ fs [llistTheory.LFINITE_THM])
  \\ simp [name_def] \\ strip_tac
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ mp_tac (fetch "-" "asm2str_app" |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
      |> Q.INST [‘xs’|->‘codegen (parser (lexer input))’,‘s’|->‘init_state LNIL pat’])
  \\ impl_tac THEN1 (unabbrev_all_tac \\ EVAL_TAC \\ fs [llistTheory.LFINITE_THM])
  \\ simp [name_def] \\ strip_tac
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ mp_tac (print_thm |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO] |> SPEC_ALL
      |> Q.INST [‘str’|->‘asm2str (codegen (parser (lexer input)))’,
                 ‘s’|->‘init_state LNIL pat’])
  \\ impl_tac THEN1 (unabbrev_all_tac \\ EVAL_TAC
                     \\ fs [llistTheory.LFINITE_THM,print_code_def,name_def])
  \\ simp [name_def] \\ strip_tac
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ simp [init_state_def]
QED

val _ = export_theory();
