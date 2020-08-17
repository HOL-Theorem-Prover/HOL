
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory x64asm_syntaxTheory mp_then
     BasicProvers source_semanticsTheory source_propertiesTheory alignmentTheory
     combinTheory optionTheory alistTheory wordsTheory wordsLib
     x64asm_syntaxTheory x64asm_semanticsTheory x64asm_propertiesTheory
     codegenTheory relationTheory lprefix_lubTheory llistTheory;

val _ = new_theory "codegen_proofs";


(* definitions of invariants and relations *)

Definition code_in_def:
  code_in n [] code = T ∧
  code_in n (x::xs) code =
    (lookup n code = SOME x ∧ code_in (n+1) xs code)
End

Definition init_code_in_def:
  init_code_in instructions ⇔
    ∃start. code_in 0 (init start) instructions
End

Definition code_rel_def:
  code_rel fs ds instructions ⇔
    init_code_in instructions ∧
    ∀n params body.
      lookup_fun n ds = SOME (params,body) ⇒
      ∃pos. ALOOKUP fs n = SOME pos ∧
            code_in pos (flatten (FST
              (c_defun pos fs (Defun n params body))) []) instructions
End

Definition state_rel_def:
  state_rel fs (s:source_semantics$state) (t:x64asm_semantics$state) ⇔
    s.input = t.input ∧
    s.output = t.output ∧
    code_rel fs s.funs t.instructions ∧
    ∃r14 r15.
      t.regs R12 = SOME 16w ∧
      t.regs R13 = SOME 0x7FFFFFFFFFFFFFFFw ∧
      t.regs R14 = SOME r14 ∧
      t.regs R15 = SOME r15 ∧
      memory_writable r14 r15 t.memory
End

Definition has_stack_def:
  has_stack t xs <=>
    ∃w ws. xs = Word w :: ws ∧ t.regs RAX = SOME w ∧ t.stack = ws
End

Definition v_inv_def:
  v_inv t (Num n) w = (n < 2 ** 63 ∧ w = n2w n) ∧
  v_inv t (Pair x1 x2) w =
    ∃w1 w2.
      read_mem (w+0w) t = SOME w1 ∧ v_inv t x1 w1 ∧
      read_mem (w+8w) t = SOME w2 ∧ v_inv t x2 w2 ∧
      w ≠ 0w (* the address must not be the null pointer *)
End

Definition env_ok_def:
  env_ok env vs curr t <=>
    LENGTH vs = LENGTH curr ∧
    ∀n v. env n = SOME v ⇒
          find n vs 0 < LENGTH curr ∧
          ∃w. EL (find n vs 0) curr = (Word w) ∧ v_inv t v w
End


(* setting up the proof goal *)

val goal =
  ``λenv e s.
      ∀res s1 t tail' vs fs cs l1 curr rest.
        eval env e s = (res,s1) ∧ res ≠ Err Crash ∧
        c_exp tail' t.pc vs fs e = (cs,l1) ∧
        state_rel fs s t ∧ env_ok env vs curr t ∧
        has_stack t (curr ++ rest) ∧ ODD (LENGTH rest) ∧
        code_in t.pc (flatten cs []) t.instructions ⇒
        ∃outcome.
          steps (State t,s.clock) outcome ∧
          case outcome of
          | (Halt ec output, ck) => output ≼ s1.output ∧ ec = 1w
          | (State t1, ck) =>
              state_rel fs s1 t1 ∧ ck = s1.clock ∧
              ∀v. res = Res v ==>
                  ∃w. v_inv t1 v w ∧
                     if tail' then
                       has_stack t1 (Word w :: rest) ∧ fetch t1 = SOME Ret
                     else
                       has_stack t1 (Word w :: curr ++ rest) ∧ t1.pc = l1``

val goals =
  ``λenv es s.
      ∀res s1 t vs fs cs l1 curr rest.
        evals env es s = (res,s1) ∧ res ≠ Err Crash ∧
        c_exps t.pc vs fs es = (cs,l1) ∧
        state_rel fs s t ∧ env_ok env vs curr t ∧
        has_stack t (curr ++ rest) ∧ ODD (LENGTH rest) ∧
        code_in t.pc (flatten cs []) t.instructions ⇒
        ∃outcome.
          steps (State t,s.clock) outcome ∧
          case outcome of
          | (Halt ec output,ck) => output ≼ s1.output ∧ ec = 1w
          | (State t1,ck) =>
              state_rel fs s1 t1 ∧ ck = s1.clock ∧
              ∀vs. res = Res vs ==>
                   ∃ws. LIST_REL (v_inv t1) vs ws ∧
                        has_stack t1 (MAP Word (REVERSE ws) ++ curr ++ rest) ∧
                        t1.pc = l1``

local
  val ind_thm = eval_ind |> ISPECL [goal,goals]
    |> CONV_RULE (DEPTH_CONV BETA_CONV) |> REWRITE_RULE [];
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> ASSUME |> CONJUNCTS |> map concl
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
  fun strip tm = tm |> ASSUME |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL |> concl
end


(* various lemmas *)

Theorem even_len_simp[simp]:
  ∀xs. even_len xs = EVEN (LENGTH xs) ∧ odd_len xs = ODD (LENGTH xs)
Proof
  Induct \\ fs [even_len_def,ODD,EVEN_ODD]
QED

Theorem steps_v_inv:
  steps (State t0,n) (State t1,m) ∧ v_inv t0 a w ⇒ v_inv t1 a w
Proof
  rw [] \\ pop_assum mp_tac
  \\ qid_spec_tac ‘w’ \\ Induct_on ‘a’ \\ fs [v_inv_def]
  \\ imp_res_tac steps_consts \\ fs [] \\ metis_tac []
QED

Theorem flatten_acc:
  ∀p acc. flatten p acc = flatten p [] ++ acc
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct_on ‘p’ \\ simp_tac std_ss [flatten_def] \\ fs []
  \\ last_assum (once_rewrite_tac o single o GSYM)
  \\ first_assum (once_rewrite_tac o single o GSYM)
  \\ fs []
QED

Theorem code_in_append[simp]:
  ∀xs ys n code.
    code_in n (xs ++ ys) code ⇔
    code_in n xs code ∧ code_in (n + LENGTH xs) ys code
Proof
  Induct \\ fs [code_in_def,ADD1,AC CONJ_COMM CONJ_ASSOC]
QED

Theorem c_exp_length:
  (∀t l vs fs x c l1. c_exp t l vs fs x = (c,l1) ⇒ l1 = l + LENGTH (flatten c [])) ∧
  (∀l vs fs xs c l1. c_exps l vs fs xs = (c,l1) ⇒ l1 = l + LENGTH (flatten c []))
Proof
  ho_match_mp_tac c_exp_ind_alt \\ rw [] \\ fs [c_exp_alt]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [] \\ fs [flatten_def]
  \\ rw [] \\ fs [c_if_def,c_test_def]
  \\ rw [] \\ fs [flatten_def]
  \\ rw [] \\ fs [c_if_def,c_test_def,c_const_def,AllCaseEqs()]
  \\ rw [] \\ fs [c_if_def,c_test_def,c_const_def,AllCaseEqs(),c_var_def,make_ret_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ Cases_on ‘c_exps l vs fs xs’ \\ fs [c_call_def]
  \\ every_case_tac
  \\ rw [] \\ fs [c_if_def,c_test_def,c_const_def,AllCaseEqs(),c_var_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def]
  \\ fs [make_ret_def]
  \\ rw [] \\ fs [c_if_def,c_test_def,c_const_def,AllCaseEqs(),c_var_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def]
  \\ rpt (pop_assum mp_tac)
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def]
  \\ rw [] \\ Cases_on ‘test’ \\ fs [c_test_def]
QED

Theorem find_acc:
  ∀n vs k. find n vs k = find n vs 0 + k
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct_on ‘vs’ \\ fs [find_def] \\ rw []
  \\ Cases_on ‘h’ \\ fs [find_def]
  \\ last_assum (once_rewrite_tac o single o GSYM)
  \\ decide_tac
QED

Theorem v_inv_ignore[simp]:
  v_inv (t with stack := s) a w = v_inv t a w ∧
  v_inv (t with pc := p) a w = v_inv t a w ∧
  v_inv (t with regs := r) a w = v_inv t a w
Proof
  qid_spec_tac ‘w’ \\ Induct_on ‘a’ \\ fs [v_inv_def,read_mem_def]
QED

fun is_bool tm = type_of tm = type_of T;

Theorem bool_ind:
  ∀P. P F ∧ (P F ⇒ P T) ⇒ ∀b. P b
Proof
  rw [] \\ Cases_on ‘b’ \\ fs []
QED

Theorem has_stack_even:
  has_stack t xs ⇒ EVEN (LENGTH t.stack) = ODD (LENGTH xs)
Proof
  fs [has_stack_def] \\ rw [] \\ fs [ODD,EVEN_ODD]
QED

Theorem memory_writable_new:
  memory_writable x y m ∧ x ≠ y:word64 ⇒
  can_write_mem_at m x ∧
  can_write_mem_at m (x + 8w) ∧
  x ≠ 0w ∧
  ∀w1 w2. memory_writable (x+16w) y ((x+8w =+ SOME w2) ((x =+ SOME w1) m))
Proof
  fs [memory_writable_def] \\ strip_tac
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs []
  \\ fs [WORD_LS] \\ fs [aligned_w2n]
  \\ fs [MOD_EQ_0_DIVISOR] \\ rpt var_eq_tac \\ fs []
  \\ fs [WORD_LO,word_add_n2w] \\ rw []
  THEN1
   (first_x_assum match_mp_tac
    \\ fs [WORD_LO] \\ qexists_tac ‘2 * d’ \\ fs [])
  THEN1
   (first_x_assum match_mp_tac
    \\ fs [WORD_LO] \\ qexists_tac ‘2 * d + 1’ \\ fs [])
  THEN1 (qexists_tac ‘d + 1’ \\ fs [])
  \\ fs [PULL_EXISTS]
  \\ fs [can_write_mem_def,APPLY_UPDATE_THM]
  \\ Cases_on ‘a’ \\ fs []
QED

Theorem v_inv_update:
  ∀t v w a b x y.
    v_inv t v w ∧
    t.memory a = SOME NONE ∧
    t.memory b = SOME NONE ⇒
    v_inv (t with memory := (b =+ y) ((a =+ x) t.memory)) v w
Proof
  Induct_on ‘v’ \\ fs [v_inv_def]
  \\ fs [read_mem_def,APPLY_UPDATE_THM]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
QED

Triviality blast_lemma = blastLib.BBLAST_PROVE “w ≠ w + 8w:word64”;

val step_tac =
  ho_match_mp_tac IMP_step \\ fs []
  \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
  \\ simp [take_branch_cases,APPLY_UPDATE_THM,PULL_EXISTS,set_pc_def]
  \\ fs [write_reg_def,has_stack_def,inc_def,set_pc_def,set_stack_def,
         EVEN,APPLY_UPDATE_THM,ODD,ODD_ADD,blast_lemma,write_mem_def,
         EVEN_ODD,ODD,take_branch_cases,unset_reg_def];

Theorem give_up:
  code_rel fs ds t.instructions ∧
  t.regs R15 = SOME w ∧
  t.pc = give_up (ODD (LENGTH t.stack)) ⇒
  steps (State t,n) (Halt 1w t.output,n)
Proof
  fs [code_rel_def,init_code_in_def,init_def,code_in_def] \\ rw []
  THEN1
   (match_mp_tac steps_trans
    \\ ntac 3 step_tac
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ once_rewrite_tac [steps_cases] \\ fs [])
  \\ match_mp_tac steps_trans
  \\ ntac 2 step_tac
  \\ ho_match_mp_tac IMP_start \\ fs []
  \\ once_rewrite_tac [steps_cases] \\ fs []
QED


(* proving the cases *)

Theorem c_exp_Const:
  ^(get_goal "eval _ (Const _)")
Proof
  CONV_TAC (RESORT_FORALL_CONV
    (fn tms => filter is_bool tms @ filter (not o is_bool) tms))
  \\ ho_match_mp_tac bool_ind
  \\ fs [] \\ reverse (rw [])
  THEN1
   (qpat_x_assum ‘c_exp T _ _ _ _ = _’ mp_tac
    \\ simp [Once c_exp_alt]
    \\ Cases_on ‘c_exp F t.pc vs fs (Const n)’ \\ fs []
    \\ fs [make_ret_def]
    \\ rw [] \\ fs [flatten_def]
    \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
    \\ fs [flatten_def]
    \\ once_rewrite_tac [flatten_acc] \\ fs []
    \\ rw [] \\ first_x_assum drule \\ fs []
    \\ rpt (disch_then drule) \\ rw []
    \\ Cases_on ‘outcome’ \\ fs []
    \\ reverse (Cases_on ‘q'’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ reverse (Cases_on ‘res’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ rw [] \\ rename [‘steps (State t0,s0.clock) (State t1,s1.clock)’]
    \\ fs [has_stack_def]
    \\ qpat_x_assum ‘_ = t1.stack’ (assume_tac o GSYM)
    \\ qexists_tac ‘State (t1 with <| pc := t1.pc + 1; stack := rest |>), s1.clock’
    \\ fs [code_in_def,state_rel_def,fetch_def]
    \\ imp_res_tac c_exp_length \\ fs []
    \\ imp_res_tac steps_inst \\ fs []
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 2)
    \\ ‘fetch t1 = SOME (Add_RSP (LENGTH vs))’ by fs [fetch_def]
    \\ once_rewrite_tac [step_cases] \\ fs []
    \\ fs [set_stack_def,inc_def,state_component_equality]
    \\ qexists_tac ‘curr’ \\ fs [env_ok_def])
  \\ fs [eval_def] \\ rw [] \\ fs [v_inv_def,PULL_EXISTS]
  \\ reverse (fs [c_exp_alt,c_const_def,AllCaseEqs()]) \\ rw []
  \\ TRY
   (qabbrev_tac ‘ss = curr ++ rest’
    \\ fs [has_stack_def,flatten_def,code_in_def]
    \\ ho_match_mp_tac IMP_step \\ fs []
    \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
    \\ fs [write_reg_def,inc_def,APPLY_UPDATE_THM,set_pc_def,set_stack_def]
    \\ ho_match_mp_tac IMP_step \\ fs []
    \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
    \\ fs [write_reg_def,inc_def,APPLY_UPDATE_THM,set_pc_def,set_stack_def]
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ fs [state_rel_def,APPLY_UPDATE_THM] \\ NO_TAC)
  \\ imp_res_tac has_stack_even
  \\ pop_assum (assume_tac o GSYM)
  \\ fs [has_stack_def,flatten_def,code_in_def]
  \\ ho_match_mp_tac IMP_step \\ fs []
  \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
  \\ fs [write_reg_def,inc_def,APPLY_UPDATE_THM,set_pc_def,set_stack_def,
         take_branch_cases]
  \\ qmatch_goalsub_abbrev_tac ‘State t1’
  \\ ‘state_rel fs s t1’ by fs [state_rel_def,Abbr‘t1’]
  \\ fs [state_rel_def]
  \\ drule give_up \\ fs []
  \\ fs [Abbr‘t1’]
  \\ fs [env_ok_def,EVEN_ODD] \\ rfs []
  \\ disch_then (qspec_then ‘s.clock’ mp_tac)
  \\ ‘ODD (LENGTH curr) = ODD (LENGTH t.stack)’ by
   (Cases_on ‘curr’ \\ fs []
    \\ Cases_on ‘rest’ \\ fs [ODD,EVEN_ODD]
    \\ qpat_x_assum ‘_ = t.stack’ (assume_tac o GSYM) \\ fs [ODD_ADD])
  \\ fs [] \\ strip_tac
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
QED

Theorem c_exp_Var:
  ^(get_goal "eval _ (Var _)")
Proof
  CONV_TAC (RESORT_FORALL_CONV
    (fn tms => filter is_bool tms @ filter (not o is_bool) tms))
  \\ ho_match_mp_tac bool_ind
  \\ fs [] \\ reverse (rw [])
  THEN1
   (qpat_x_assum ‘c_exp T _ _ _ _ = _’ mp_tac
    \\ simp [Once c_exp_alt]
    \\ rename [‘Var v’] \\ rename [‘state_rel _ s t’]
    \\ Cases_on ‘c_exp F t.pc vs fs (Var v)’ \\ fs []
    \\ fs [make_ret_def]
    \\ rw [] \\ fs [flatten_def]
    \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
    \\ fs [flatten_def]
    \\ once_rewrite_tac [flatten_acc] \\ fs []
    \\ rw [] \\ first_x_assum drule \\ fs []
    \\ rpt (disch_then drule) \\ rw []
    \\ Cases_on ‘outcome’ \\ fs []
    \\ reverse (Cases_on ‘q'’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ reverse (Cases_on ‘res’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ rw [] \\ rename [‘steps (State t0,s0.clock) (State t1,s1.clock)’]
    \\ fs [has_stack_def]
    \\ qpat_x_assum ‘_ = t1.stack’ (assume_tac o GSYM)
    \\ qexists_tac ‘State (t1 with <| pc := t1.pc + 1; stack := rest |>), s1.clock’
    \\ fs [code_in_def,state_rel_def,fetch_def]
    \\ imp_res_tac c_exp_length \\ fs []
    \\ imp_res_tac steps_inst \\ fs []
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 2)
    \\ ‘fetch t1 = SOME (Add_RSP (LENGTH vs))’ by fs [fetch_def]
    \\ once_rewrite_tac [step_cases] \\ fs []
    \\ fs [set_stack_def,inc_def,state_component_equality]
    \\ qexists_tac ‘curr’ \\ fs [env_ok_def])
  \\ fs [eval_def,AllCaseEqs()] \\ rw []
  \\ rename [‘Var v’] \\ rename [‘state_rel _ s t’]
  \\ fs [env_ok_def]
  \\ first_x_assum drule \\ rw []
  \\ fs [c_exp_alt,c_var_def]
  \\ fs [AllCaseEqs()] \\ rw []
  \\ fs [flatten_def,code_in_def]
  THEN1
   (Cases_on ‘vs’ \\ fs [] \\ rw [] \\ fs [] \\ fs [find_def]
    \\ qpat_x_assum ‘_ = 0’ mp_tac
    \\ once_rewrite_tac [find_acc] \\ fs [AllCaseEqs()]
    \\ rw [] \\ Cases_on ‘curr’ \\ fs []
    \\ fs [has_stack_def] \\ rw []
    \\ qexists_tac ‘(State (t with <| pc := t.pc+1; stack := Word w::t.stack |>), s.clock)’
    \\ fs [] \\ fs [state_rel_def]
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 2)
    \\ ‘fetch t = SOME (Push RAX)’ by fs [fetch_def]
    \\ once_rewrite_tac [step_cases] \\ fs []
    \\ fs [set_stack_def,inc_def,state_component_equality])
  \\ rename [‘k < LENGTH _’]
  \\ qexists_tac ‘(State (t with <| pc := t.pc+2;
       regs := (RAX =+ SOME w) t.regs;
       stack := (HD curr) :: t.stack |>), s.clock)’
  \\ fs [state_rel_def]
  \\ fs [has_stack_def,APPLY_UPDATE_THM]
  \\ Cases_on ‘curr’ \\ fs [] \\ rpt var_eq_tac
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
  \\ qexists_tac ‘State (t with <| pc := t.pc+1;
       stack := Word w' :: t.stack |>)’
  \\ qexists_tac ‘s.clock’ \\ rw []
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 2)
  \\ once_rewrite_tac [step_cases] \\ fs [fetch_def]
  \\ fs [set_stack_def,inc_def,write_reg_def,state_component_equality]
  \\ qexists_tac ‘w’ \\ fs []
  \\ qpat_x_assum ‘_ = t.stack’ (assume_tac o GSYM) \\ fs []
  \\ Cases_on ‘k’ \\ fs [rich_listTheory.EL_APPEND1]
QED

val op_init_tac =
  rw [] \\ fs [eval_def,c_exp_alt]
  \\ Cases_on ‘evals env xs s’ \\ fs []
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
  \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [] \\ rw []
  \\ Cases_on ‘q = Err Crash’ \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ rpt (disch_then drule) \\ rw []
  \\ reverse (Cases_on ‘q’) \\ fs [] \\ rw []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ imp_res_tac eval_op_mono
  \\ Cases_on ‘outcome’ \\ fs []
  \\ reverse (Cases_on ‘q’) \\ fs []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
         \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS)
  \\ rename [‘eval_op _ vs s0 = _’]
  \\ first_x_assum (qspec_then ‘vs’ strip_assume_tac) \\ fs [] \\ rw []
  \\ rename [‘steps (State t1,s1.clock) (State t2,s2.clock)’]
  \\ ho_match_mp_tac IMP_steps \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ imp_res_tac c_exp_length
  \\ fs [c_op_def,c_head_def,c_tail_def,c_cons_def,c_add_def,c_sub_def,
         c_div_def,c_read_def,c_write_def,code_in_def]
  \\ imp_res_tac steps_inst;

Theorem c_exp_Cons:
  ~tail' ∧ f = Cons ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def]
  \\ rw [] \\ fs [env_ok_def] \\ rw [] \\ fs [] \\ rfs []
  \\ imp_res_tac has_stack_even
  \\ fs [has_stack_def]
  \\ qpat_x_assum ‘_ = t2.stack’ (assume_tac o GSYM)
  \\ ‘init_code_in t1.instructions’ by fs [state_rel_def,code_rel_def]
  \\ fs [init_code_in_def,code_in_def,init_def,EVEN,ODD]
  THEN1
   (ho_match_mp_tac IMP_step \\ fs []
    \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
    \\ fs [write_reg_def,has_stack_def,inc_def,set_pc_def,set_stack_def]
    \\ ntac 2 step_tac
    \\ fs [state_rel_def]
    \\ IF_CASES_TAC \\ rw []
    THEN1 (ntac 3 step_tac \\ ho_match_mp_tac IMP_start \\ fs [])
    \\ drule memory_writable_new \\ fs [] \\ strip_tac
    \\ fs [can_write_mem_def]
    \\ ntac 6 step_tac
    \\ ho_match_mp_tac IMP_start \\ fs [APPLY_UPDATE_THM]
    \\ fs [v_inv_def,read_mem_def,APPLY_UPDATE_THM,blast_lemma]
    \\ rw [] \\ match_mp_tac v_inv_update \\ fs [])
  THEN1
   (ho_match_mp_tac IMP_step \\ fs []
    \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
    \\ fs [write_reg_def,has_stack_def,inc_def]
    \\ ntac 2 step_tac
    \\ fs [state_rel_def,ODD,EVEN]
    \\ IF_CASES_TAC \\ rw []
    THEN1 (ntac 3 step_tac \\ ho_match_mp_tac IMP_start \\ fs [])
    \\ drule memory_writable_new \\ fs [] \\ strip_tac
    \\ fs [can_write_mem_def]
    \\ ntac 5 step_tac
    \\ ho_match_mp_tac IMP_start \\ fs [APPLY_UPDATE_THM]
    \\ fs [v_inv_def,read_mem_def,APPLY_UPDATE_THM,blast_lemma]
    \\ rw [] \\ match_mp_tac v_inv_update \\ fs [])
QED

Theorem c_exp_Head:
  ~tail' ∧ f = Head ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac \\ step_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [has_stack_def,wordsTheory.w2w_def,v_inv_def]
  \\ ho_match_mp_tac IMP_start \\ fs []
  \\ fs [write_reg_def,inc_def,state_rel_def,APPLY_UPDATE_THM]
QED

Theorem c_exp_Tail:
  ~tail' ∧ f = Tail ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac \\ step_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [has_stack_def,wordsTheory.w2w_def,v_inv_def]
  \\ ho_match_mp_tac IMP_start \\ fs []
  \\ fs [write_reg_def,inc_def,state_rel_def,APPLY_UPDATE_THM]
QED

Theorem c_exp_Add:
  ~tail' ∧ f = Add ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [] \\ rw [] \\ fs [v_inv_def,GSYM PULL_FORALL] \\ rw [] \\ fs []
  \\ imp_res_tac has_stack_even
  \\ fs [has_stack_def]
  \\ qpat_x_assum ‘_ = t2.stack’ (assume_tac o GSYM)
  \\ ntac 3 step_tac
  \\ fs [state_rel_def,word_add_n2w]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 (ho_match_mp_tac IMP_start \\ fs [APPLY_UPDATE_THM]
         \\ fs [v_inv_def,read_mem_def,FLOOKUP_UPDATE,blast_lemma])
  \\ qmatch_goalsub_abbrev_tac ‘State t3,nn’
  \\ ‘code_rel fs s1.funs t3.instructions’ by fs [Abbr‘t3’]
  \\ drule give_up
  \\ fs [Abbr‘t3’,APPLY_UPDATE_THM,ODD,EVEN_ODD,env_ok_def]
  \\ disch_then (qspec_then ‘nn’ assume_tac)
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
QED

Theorem c_exp_Sub:
  ~tail' ∧ f = Sub ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [] \\ rw [] \\ fs [v_inv_def] \\ rw [] \\ fs []
  \\ step_tac
  \\ qpat_x_assum ‘_ = t2.stack’ (assume_tac o GSYM) \\ fs [set_stack_def]
  \\ step_tac
  \\ IF_CASES_TAC \\ fs [NOT_LESS]
  \\ imp_res_tac (DECIDE “n ≤ m ⇒ n-m=0”) \\ asm_rewrite_tac []
  \\ simp [GSYM PULL_FORALL,v_inv_def,set_pc_def]
  THEN1
   (ntac 2 step_tac
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ fs [write_reg_def,inc_def,state_rel_def,APPLY_UPDATE_THM]
    \\ rename [‘n < m’] \\ ‘n ≤ m’ by fs []
    \\ fs [LESS_EQ_EXISTS] \\ rw [] \\ fs [GSYM word_add_n2w])
  \\ ntac 3 step_tac
  \\ ho_match_mp_tac IMP_start \\ fs []
  \\ fs [write_reg_def,inc_def,state_rel_def,APPLY_UPDATE_THM]
QED

Theorem c_exp_Div:
  ~tail' ∧ f = Div ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [] \\ rw [] \\ fs [] \\ step_tac
  \\ qpat_x_assum ‘_ = t2.stack’ (assume_tac o GSYM)
  \\ ntac 3 step_tac
  \\ fs [v_inv_def] \\ rw [] \\ fs []
  \\ ho_match_mp_tac IMP_start \\ fs []
  \\ fs [state_rel_def,v_inv_def,DIV_LT_X,APPLY_UPDATE_THM]
QED

Theorem c_exp_Read:
  ~tail' ∧ f = Read ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [] \\ rw [] \\ fs [v_inv_def,GSYM PULL_FORALL,align_def]
  \\ rename [‘env_ok env vs curr t1’]
  \\ Cases_on ‘EVEN (LENGTH vs)’ \\ fs [code_in_def]
  THEN1
   (fs [has_stack_def]
    \\ ntac 3 step_tac
    \\ ‘ODD (LENGTH (curr ++ rest))’ by
          (rewrite_tac [LENGTH_APPEND] \\ rfs [EVEN_ODD,ODD_ADD,env_ok_def])
    \\ pop_assum mp_tac \\ asm_rewrite_tac [LENGTH,EVEN]
    \\ simp [LENGTH,EVEN,ODD_EVEN] \\ rw []
    \\ Cases_on ‘t2.input’ \\ fs [PULL_EXISTS,read_char_def]
    \\ step_tac \\ ho_match_mp_tac IMP_start \\ fs []
    \\ ‘ORD h < 256’ by fs [ORD_BOUND]
    \\ fs [state_rel_def,v_inv_def,APPLY_UPDATE_THM,next_def])
  THEN1
   (fs [has_stack_def]
    \\ ntac 2 step_tac
    \\ ‘EVEN (LENGTH (curr ++ rest))’ by
          (rewrite_tac [LENGTH_APPEND] \\ rfs [EVEN_ODD,ODD_ADD,env_ok_def])
    \\ pop_assum mp_tac
    \\ asm_rewrite_tac [LENGTH,EVEN]
    \\ simp [LENGTH,EVEN,ODD_EVEN] \\ rw []
    \\ Cases_on ‘t2.input’ \\ fs [PULL_EXISTS,read_char_def]
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ ‘ORD h < 256’ by fs [ORD_BOUND]
    \\ fs [state_rel_def,v_inv_def,APPLY_UPDATE_THM,next_def])
QED

Theorem c_exp_Write:
  ~tail' ∧ f = Write ⇒
  ^(strip (get_goal "eval _ (Op _ _)"))
Proof
  op_init_tac
  \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [] \\ rw [] \\ fs [v_inv_def,GSYM PULL_FORALL,align_def]
  \\ rename [‘env_ok env vs curr t1’]
  \\ Cases_on ‘EVEN (LENGTH vs)’ \\ fs [code_in_def]
  THEN1
   (ntac 3 step_tac
    \\ CONV_TAC (RESORT_EXISTS_CONV rev) \\ rfs []
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ ‘ODD (LENGTH (curr ++ rest))’ by
          (rewrite_tac [LENGTH_APPEND] \\ rfs [EVEN_ODD,ODD_ADD,env_ok_def])
    \\ pop_assum mp_tac
    \\ asm_rewrite_tac [LENGTH,EVEN]
    \\ simp [LENGTH,EVEN,ODD_EVEN] \\ rw []
    \\ fs [unset_reg_def,put_char_def]
    \\ ntac 2 step_tac
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ fs [state_rel_def,APPLY_UPDATE_THM])
  THEN1
   (ntac 2 step_tac
    \\ CONV_TAC (RESORT_EXISTS_CONV rev) \\ rfs []
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ ‘EVEN (LENGTH (curr ++ rest))’ by
          (rewrite_tac [LENGTH_APPEND] \\ rfs [EVEN_ODD,ODD_ADD,env_ok_def])
    \\ pop_assum mp_tac
    \\ asm_rewrite_tac [LENGTH,EVEN]
    \\ simp [LENGTH,EVEN,ODD_EVEN] \\ rw []
    \\ fs [unset_reg_def,put_char_def]
    \\ step_tac
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ fs [state_rel_def,APPLY_UPDATE_THM])
QED

Theorem c_exp_Op:
  ^(get_goal "eval _ (Op _ _)")
Proof
  fs [PULL_FORALL]
  \\ CONV_TAC (RESORT_FORALL_CONV
       (fn tms => filter is_bool tms @ filter (not o is_bool) tms))
  \\ ho_match_mp_tac bool_ind
  \\ fs [] \\ reverse (rw [])
  THEN1
   (qpat_x_assum ‘c_exp T _ _ _ _ = _’ mp_tac
    \\ simp [Once c_exp_alt]
    \\ Cases_on ‘c_exp F t.pc vs fs (Op f xs)’ \\ fs []
    \\ fs [make_ret_def]
    \\ rw [] \\ fs [flatten_def]
    \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
    \\ fs [flatten_def]
    \\ once_rewrite_tac [flatten_acc] \\ fs []
    \\ rw [] \\ first_x_assum drule \\ fs []
    \\ rpt (disch_then drule) \\ rw []
    \\ Cases_on ‘outcome’ \\ fs []
    \\ reverse (Cases_on ‘q'’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ reverse (Cases_on ‘res’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ rw [] \\ rename [‘steps (State t0,s0.clock) (State t1,s1.clock)’]
    \\ last_x_assum kall_tac
    \\ first_x_assum (qspec_then ‘a’ mp_tac) \\ fs [] \\ strip_tac
    \\ fs [has_stack_def]
    \\ qpat_x_assum ‘_ = t1.stack’ (assume_tac o GSYM)
    \\ qexists_tac ‘State (t1 with <| pc := t1.pc + 1; stack := rest |>), s1.clock’
    \\ fs [code_in_def,state_rel_def,fetch_def]
    \\ imp_res_tac c_exp_length \\ fs []
    \\ imp_res_tac steps_inst \\ fs []
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 2)
    \\ ‘fetch t1 = SOME (Add_RSP (LENGTH vs))’ by fs [fetch_def]
    \\ once_rewrite_tac [step_cases] \\ fs []
    \\ fs [set_stack_def,inc_def,state_component_equality]
    \\ qexists_tac ‘curr’ \\ fs [env_ok_def])
  \\ Cases_on ‘f’ \\ rw []
  \\ EVERY ([c_exp_Cons, c_exp_Head, c_exp_Tail, c_exp_Add,
             c_exp_Sub, c_exp_Div, c_exp_Read, c_exp_Write]
       |> map (drule o SIMP_RULE std_ss [] o GEN_ALL))
  \\ rpt (disch_then (fn th => (drule_all th \\ strip_tac) ORELSE all_tac))
  \\ qexists_tac ‘outcome’ \\ fs []
QED

Theorem c_test_thm:
  state_rel fs s t ∧
  LIST_REL (v_inv t) args ws ∧
  take_branch test args s = (Res b,s) ∧
  has_stack t (MAP Word (REVERSE ws) ⧺ rest) ∧
  has_stack k rest ∧
  code_in t.pc (c_test test l4) t.instructions ⇒
  ∃t1.
    steps (State t,s.clock) (State t1,s.clock) ∧
    state_rel fs s t1 ∧ has_stack t1 rest ∧
    t1.pc = if b then l4 else t.pc + 4
Proof
  Cases_on ‘test’ \\ fs []
  \\ fs [source_semanticsTheory.take_branch_def,fail_def,AllCaseEqs(),return_def]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ fs [v_inv_def] \\ rw []
  \\ fs [has_stack_def]
  \\ qpat_x_assum ‘_ = _.stack’ (assume_tac o GSYM) \\ fs []
  \\ fs [c_test_def,code_in_def]
  \\ ho_match_mp_tac IMP_steps_state
  \\ ntac 4 (ho_match_mp_tac IMP_step \\ fs []
             \\ once_rewrite_tac [step_cases] \\ fs [fetch_def]
             \\ fs [write_reg_def,has_stack_def,inc_def,set_stack_def])
  \\ fs [x64asm_semanticsTheory.take_branch_cases,PULL_EXISTS,
         APPLY_UPDATE_THM,set_pc_def]
  \\ qmatch_goalsub_abbrev_tac ‘State tt’
  \\ qexists_tac ‘(State tt,s.clock)’ \\ fs []
  \\ qexists_tac ‘tt’ \\ fs []
  \\ once_rewrite_tac [steps_cases] \\ fs []
  \\ rw [Abbr‘tt’] \\ fs [state_rel_def,APPLY_UPDATE_THM]
QED

Theorem c_exp_If:
  ^(get_goal "eval _ (If _ _ _ _)")
Proof
  rw [] \\ fs [eval_def,c_exp_alt,c_if_def]
  \\ Cases_on ‘evals env xs s’ \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
  \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ rpt strip_tac \\ rpt var_eq_tac \\ fs [code_in_def]
  \\ Cases_on ‘q = Err Crash’ \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ rpt (disch_then drule) \\ rw []
  \\ reverse (Cases_on ‘q’) \\ fs [] \\ rw []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ rename [‘take_branch test args s5’]
  \\ Cases_on ‘take_branch test args s5’ \\ fs []
  \\ rename [‘_ = (taken,s6)’]
  \\ ‘s6 = s5’ by
    (fs [AllCaseEqs(),source_semanticsTheory.take_branch_def,fail_def,return_def] \\ rw [])
  \\ rw []
  \\ PairCases_on ‘outcome’ \\ fs []
  \\ reverse (Cases_on ‘outcome0’) \\ fs []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
         \\ fs [AllCaseEqs()]
         \\ rw [] \\ fs [] \\ imp_res_tac eval_mono
         \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ fs [])
  \\ qpat_x_assum ‘_ = (res,s1)’ mp_tac
  \\ simp [AllCaseEqs(),source_semanticsTheory.take_branch_def,fail_def,
           return_def,PULL_EXISTS]
  \\ reverse (rw []) \\ fs []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ rfs [] \\ rename [‘state_rel fs s5 t5’]
  \\ imp_res_tac c_exp_length \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ ho_match_mp_tac IMP_steps \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ pop_assum (assume_tac o GSYM)
  \\ qmatch_asmsub_abbrev_tac ‘c_test _ l4’ \\ fs []
  \\ ‘LENGTH (c_test test l4) = 4’ by (Cases_on ‘test’ \\ fs [c_test_def])
  \\ fs []
  \\ ‘t.instructions = t5.instructions’ by (imp_res_tac steps_inst \\ fs []) \\ fs []
  \\ drule_all (c_test_thm |> Q.INST [‘rest’|->‘curr++rest’]
                  |> SIMP_RULE (srw_ss()) [])
  \\ strip_tac
  \\ ho_match_mp_tac IMP_steps \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ pop_assum (assume_tac o GSYM)
  \\ Cases_on ‘b’ \\ fs []
  THEN1
   (first_x_assum drule \\ fs []
    \\ disch_then (qspecl_then [‘curr’,‘rest’] mp_tac)
    \\ reverse impl_tac THEN1 (metis_tac [])
    \\ fs [] \\ imp_res_tac steps_inst \\ fs []
    \\ fs [env_ok_def] \\ rw [] \\ res_tac \\ fs []
    \\ imp_res_tac steps_v_inv \\ fs []
    \\ Cases_on ‘tail'’ \\ fs [])
  \\ qpat_x_assum ‘_ = t5.pc’ (assume_tac o GSYM) \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ disch_then (qspecl_then [‘curr’,‘rest’] mp_tac)
  \\ impl_tac THEN1
   (fs [] \\ imp_res_tac steps_inst \\ fs []
    \\ fs [env_ok_def] \\ rw [] \\ res_tac \\ fs []
    \\ imp_res_tac steps_v_inv \\ fs [])
  \\ strip_tac
  \\ ho_match_mp_tac IMP_steps \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ PairCases_on ‘outcome’ \\ fs []
  \\ reverse (Cases_on ‘outcome0’) \\ fs []
  THEN1 (ho_match_mp_tac IMP_start \\ fs [])
  \\ reverse (Cases_on ‘res’) \\ fs []
  THEN1 (ho_match_mp_tac IMP_start \\ fs [])
  \\ rename [‘COND taill’] \\ Cases_on ‘taill’ \\ fs []
  THEN1 (ho_match_mp_tac IMP_start \\ fs [] \\ fs [has_stack_def])
  \\ imp_res_tac steps_inst
  \\ fs [has_stack_def,code_in_def]
  \\ step_tac
  \\ ho_match_mp_tac IMP_start \\ fs []
  \\ fs [state_rel_def]
QED

Theorem c_exp_Let:
  ^(get_goal "eval _ (Let _ _ _)")
Proof
  fs [eval_def,c_exp_alt] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt var_eq_tac
  \\ Cases_on ‘eval env x s’ \\ fs []
  \\ Cases_on ‘q = Err Crash’ \\ fs []
  \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
  \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ strip_tac
  \\ first_x_assum drule
  \\ rpt (disch_then drule)
  \\ strip_tac
  \\ Cases_on ‘outcome’
  \\ rename [‘steps _ (r1,r2)’]
  \\ reverse (Cases_on ‘r1’) \\ fs []
  THEN1
   (goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ fs [AllCaseEqs()] \\ rw []
    \\ imp_res_tac eval_mono
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS)
  \\ reverse (Cases_on ‘q’) \\ fs []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [] \\ rw [])
  \\ rename [‘eval env⦇vname ↦ SOME v⦈ y s2 = (res,s3)’] \\ rw []
  \\ first_x_assum drule \\ fs []
  \\ disch_then (qspecl_then [‘Word w :: curr’,‘rest’] mp_tac)
  \\ impl_tac THEN1
   (imp_res_tac c_exp_length \\ fs []
    \\ imp_res_tac steps_inst \\ fs []
    \\ rw [] \\ fs [env_ok_def] \\ rw []
    \\ rw [] \\ fs [find_def] \\ rw []
    \\ once_rewrite_tac [find_acc] \\ fs [ADD1]
    \\ fs [GSYM ADD1,APPLY_UPDATE_THM]
    \\ imp_res_tac steps_v_inv \\ fs [] \\ res_tac \\ fs [])
  \\ strip_tac
  \\ Cases_on ‘tail'’
  THEN1
   (qexists_tac ‘outcome’
    \\ conj_tac THEN1 (Cases_on ‘outcome’ \\ imp_res_tac steps_rules \\ fs [])
    \\ Cases_on ‘outcome’
    \\ fs [AllCaseEqs()] \\ rw []
    \\ Cases_on ‘q’ \\ fs []
    \\ imp_res_tac eval_mono
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ fs [PULL_EXISTS]
    \\ rw [] \\ rpt (goal_assum (first_assum o mp_then Any mp_tac)))
  \\ fs []
  \\ Cases_on ‘outcome’ \\ fs []
  \\ reverse (Cases_on ‘q’) \\ fs []
  THEN1
   (rename [‘steps (State s8,s2.clock) (Halt Failure out,r5)’]
    \\ qexists_tac ‘Halt Failure out,r5’ \\ fs []
    \\ imp_res_tac steps_rules \\ fs [])
  \\ reverse (Cases_on ‘res’) \\ fs []
  THEN1
   (qexists_tac ‘State s'',s3.clock’ \\ fs []
    \\ imp_res_tac steps_rules \\ fs [])
  \\ rename [‘steps (State t7,s2.clock) (State t8,s3.clock)’] \\ rw []
  \\ qexists_tac ‘(State (t8 with <| pc := t8.pc+1; stack := TL t8.stack |>), s3.clock)’
  \\ fs [] \\ rpt strip_tac
  \\ TRY (fs [state_rel_def] \\ NO_TAC)
  THEN1
   (match_mp_tac (steps_rules |> CONJUNCTS |> last)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 2)
    \\ fs [code_in_def]
    \\ imp_res_tac c_exp_length \\ fs []
    \\ imp_res_tac steps_inst \\ fs []
    \\ ‘fetch t8 = SOME (Add_RSP 1)’ by fs [fetch_def]
    \\ once_rewrite_tac [step_cases] \\ fs []
    \\ fs [set_stack_def,inc_def,state_component_equality]
    \\ qexists_tac ‘[HD t8.stack]’ \\ fs []
    \\ fs [has_stack_def]
    \\ qpat_x_assum ‘_ = t8.stack’ (assume_tac o GSYM) \\ fs [])
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [has_stack_def] \\ rfs []
  \\ metis_tac [TL]
QED

val Call_init_tac = rw [] \\ rpt (pop_assum mp_tac) \\ Cases_on ‘tail'’
val [Call_tail,Call_not_tail] =
  ([],get_goal "eval _ (Call _ _)")
  |> Call_init_tac |> fst |> map snd

Definition write_regs_def:
  write_regs [] rs = rs ∧
  write_regs ((x,y)::xs) rs = (x =+ SOME y) (write_regs xs rs)
End

Overload ARGS[inferior] = “[RDI;RDX;RBX;RBP]”

Definition pops_regs_def:
  pops_regs (ws:word64 list) rs =
    if ws = [] ∨ 5 < LENGTH ws then rs else
      write_regs (ZIP(REVERSE (TAKE ((LENGTH ws)-1) ARGS), ws)) rs
End

Theorem c_pops_thm:
  has_stack t (MAP Word (REVERSE ws) ++ rest) ∧
  code_in t.pc (c_pops (xs:exp list) (vs:num option list))
    t.instructions ∧ code_rel fs ds t.instructions ∧
  t.regs R15 = SOME r15 ∧
  LENGTH xs = LENGTH ws ∧ (EVEN (LENGTH vs) = ODD (LENGTH rest)) ⇒
  ∃outcome.
    steps (State t,n) outcome ∧
    case outcome of
    | (Halt ec output,m) => t.output = output ∧ ec = 1w
    | (State t1,m) => m = n ∧ LENGTH ws ≤ 5 ∧
                      t1 = t with <| regs := pops_regs ws t.regs;
                                     pc := t.pc + LENGTH (c_pops xs vs);
                                     stack := rest |>
Proof
  fs [c_pops_def,pops_regs_def]
  \\ Cases_on ‘xs = []’ \\ fs []
  THEN1
   (Cases_on ‘ws = []’ \\ fs []
    \\ fs [has_stack_def] \\ rw [] \\ fs [code_in_def]
    \\ step_tac
    \\ ho_match_mp_tac IMP_start
    \\ once_rewrite_tac [steps_cases] \\ fs [state_component_equality])
  \\ Cases_on ‘ws = []’ \\ fs []
  \\ IF_CASES_TAC
  THEN1
   (fs [LENGTH_EQ_NUM_compute] \\ rw [] \\ fs [ZIP_def,write_regs_def]
    \\ ho_match_mp_tac IMP_start \\ fs [state_component_equality]
    \\ fs [has_stack_def])
  \\ Cases_on ‘xs’ \\ fs [] \\ rename [‘LENGTH xs’]
  \\ Cases_on ‘xs’ \\ fs [] \\ rename [‘LENGTH xs’]
  \\ Cases_on ‘xs’ \\ fs []
  THEN1
   (fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [ZIP_def,write_regs_def,code_in_def,has_stack_def]
    \\ qpat_x_assum ‘_ = t.stack’ (assume_tac o GSYM)
    \\ step_tac
    \\ ho_match_mp_tac IMP_start
    \\ once_rewrite_tac [steps_cases] \\ fs [state_component_equality])
  \\ rename [‘LENGTH xs’] \\ Cases_on ‘xs’ \\ fs []
  THEN1
   (fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [ZIP_def,write_regs_def,code_in_def,has_stack_def]
    \\ qpat_x_assum ‘_ = t.stack’ (assume_tac o GSYM)
    \\ ntac 2 step_tac
    \\ ho_match_mp_tac IMP_start
    \\ once_rewrite_tac [steps_cases] \\ fs [state_component_equality])
  \\ rename [‘LENGTH xs’] \\ Cases_on ‘xs’ \\ fs []
  THEN1
   (fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [ZIP_def,write_regs_def,code_in_def,has_stack_def]
    \\ qpat_x_assum ‘_ = t.stack’ (assume_tac o GSYM)
    \\ ntac 3 step_tac
    \\ ho_match_mp_tac IMP_start
    \\ once_rewrite_tac [steps_cases] \\ fs [state_component_equality])
  \\ rename [‘LENGTH xs’] \\ Cases_on ‘xs’ \\ fs []
  THEN1
   (fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [ZIP_def,write_regs_def,code_in_def,has_stack_def]
    \\ qpat_x_assum ‘_ = t.stack’ (assume_tac o GSYM)
    \\ ntac 4 step_tac
    \\ ho_match_mp_tac IMP_start
    \\ once_rewrite_tac [steps_cases] \\ fs [state_component_equality])
  THEN1
   (fs [code_in_def] \\ rpt strip_tac
    \\ step_tac
    \\ qmatch_goalsub_abbrev_tac ‘State t1’
    \\ ‘code_rel fs ds t1.instructions’ by fs [Abbr‘t1’]
    \\ drule (GEN_ALL give_up)
    \\ fs [Abbr‘t1’,has_stack_def]
    \\ disch_then (qspec_then ‘n’ mp_tac)
    \\ qsuff_tac ‘ODD (LENGTH t.stack) = ODD (LENGTH ws + LENGTH vs)’
    THEN1 (strip_tac \\ fs [ODD_ADD] \\ strip_tac
           \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ ‘ODD (LENGTH t.stack) = ~ODD (LENGTH (Word w :: t.stack))’ by fs [ODD]
    \\ asm_rewrite_tac []
    \\ qpat_x_assum ‘_ = _ :: t.stack’ (assume_tac o GSYM)
    \\ asm_rewrite_tac [] \\ fs [EVEN_ODD,ODD_ADD]
    \\ fs [ODD_EVEN] \\ fs [EVEN] \\ metis_tac [])
QED

Theorem c_pushes_thm:
  c_pushes params pos = (c,vs1,l1) ∧
  code_in t.pc (flatten c []) t.instructions ∧
  t.regs = pops_regs ws regs ∧
  t.stack = rest ∧ LENGTH params ≤ 5 ∧
  t.regs RAX = SOME w ∧
  (ws ≠ [] ⇒ LAST ws = w) ∧
  LIST_REL (v_inv t) args ws ∧
  LENGTH ws = LENGTH params ∧
  state_rel fs r t ⇒
  ∃new_curr t5.
    steps (State t,n) (State t5,n) ∧
    t5.pc = t.pc + LENGTH (flatten c []) ∧
    l1 = pos + LENGTH (flatten c []) ∧
    has_stack t5 (new_curr ++ rest) ∧
    env_ok (make_env params args empty_env) vs1 new_curr t5 ∧
    state_rel fs r t5 ∧
    t5.instructions = t.instructions
Proof
  rw []
  \\ ‘(∀n. ~MEM n ARGS ⇒ regs n = t.regs n)’ by
   (fs [] \\ Cases \\ fs [pops_regs_def] \\ rw [] \\ fs []
    \\ Cases_on ‘params’ \\ fs [] \\ Cases_on ‘ws’ \\ fs [] \\ rw []
    \\ rpt (rename [‘LENGTH params = LENGTH ws’]
            \\ Cases_on ‘params’ \\ fs [] \\ Cases_on ‘ws’ \\ fs []
            \\ rw [ZIP_def,write_regs_def,APPLY_UPDATE_THM]))
  \\ Cases_on ‘ws’ \\ fs []
  THEN1
   (rw [] \\ fs [c_pushes_def] \\ rw []
    \\ fs [flatten_def,code_in_def,pops_regs_def,make_env_def]
    \\ qexists_tac ‘[Word w]’ \\ fs []
    \\ qexists_tac ‘t’ \\ fs []
    \\ fs [has_stack_def,env_ok_def,empty_env_def])
  \\ rw [] \\ rename [‘SUC (LENGTH ws)’]
  \\ Cases_on ‘ws’ \\ fs []
  THEN1
   (rw [] \\ fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [c_pushes_def] \\ rw [] \\ fs [flatten_def]
    \\ rename [‘make_env [k] [x]’]
    \\ qexists_tac ‘[Word h]’
    \\ qexists_tac ‘t’ \\ fs []
    \\ fs [has_stack_def]
    \\ fs [env_ok_def,make_env_def,APPLY_UPDATE_THM] \\ rw []
    \\ EVAL_TAC \\ fs [empty_env_def])
  \\ rw[] \\ fs [] \\ rw [] \\ rename [‘SUC (LENGTH ws)’]
  \\ Cases_on ‘ws’ \\ fs []
  THEN1
   (rw [] \\ fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [c_pushes_def] \\ rw [] \\ fs [flatten_def]
    \\ qexists_tac ‘[Word h'; Word h]’ \\ fs []
    \\ fs [code_in_def,pops_regs_def,ZIP_def,write_regs_def]
    \\ ho_match_mp_tac IMP_steps_alt
    \\ step_tac
    \\ fs [GSYM PULL_EXISTS]
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘State t1’
    \\ qexists_tac ‘t1’
    \\ fs [Abbr‘t1’,has_stack_def,APPLY_UPDATE_THM]
    \\ fs [state_rel_def,APPLY_UPDATE_THM]
    \\ fs [env_ok_def,make_env_def,empty_env_def,APPLY_UPDATE_THM]
    \\ rw [] \\ EVAL_TAC \\ fs [])
  \\ rw[] \\ fs [] \\ rw [] \\ rename [‘SUC (LENGTH ws)’]
  \\ Cases_on ‘ws’ \\ fs []
  THEN1
   (rw [] \\ fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [c_pushes_def] \\ rw [] \\ fs [flatten_def]
    \\ qexists_tac ‘[Word h''; Word h'; Word h]’ \\ fs []
    \\ fs [code_in_def,pops_regs_def,ZIP_def,write_regs_def]
    \\ ho_match_mp_tac IMP_steps_alt
    \\ ntac 2 (ho_match_mp_tac IMP_step \\ fs []
               \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
               \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,EVEN]
               \\ fs [GSYM PULL_EXISTS])
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘State t1’
    \\ qexists_tac ‘t1’
    \\ fs [Abbr‘t1’,has_stack_def,APPLY_UPDATE_THM]
    \\ fs [state_rel_def,APPLY_UPDATE_THM]
    \\ fs [env_ok_def,make_env_def,empty_env_def,APPLY_UPDATE_THM]
    \\ rw [] \\ EVAL_TAC \\ fs [])
  \\ rw[] \\ fs [] \\ rw [] \\ rename [‘SUC (LENGTH ws)’]
  \\ Cases_on ‘ws’ \\ fs []
  THEN1
   (rw [] \\ fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [c_pushes_def] \\ rw [] \\ fs [flatten_def]
    \\ qexists_tac ‘[Word h'''; Word h''; Word h'; Word h]’ \\ fs []
    \\ fs [code_in_def,pops_regs_def,ZIP_def,write_regs_def]
    \\ ho_match_mp_tac IMP_steps_alt
    \\ ntac 3 (ho_match_mp_tac IMP_step \\ fs []
               \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
               \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,EVEN]
               \\ fs [GSYM PULL_EXISTS])
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘State t1’
    \\ qexists_tac ‘t1’
    \\ fs [Abbr‘t1’,has_stack_def,APPLY_UPDATE_THM]
    \\ fs [state_rel_def,APPLY_UPDATE_THM]
    \\ fs [env_ok_def,make_env_def,empty_env_def,APPLY_UPDATE_THM]
    \\ rw [] \\ EVAL_TAC \\ fs [])
  \\ rw[] \\ fs [] \\ rw [] \\ rename [‘SUC (LENGTH ws)’]
  \\ Cases_on ‘ws’ \\ fs []
  THEN1
   (rw [] \\ fs [LENGTH_EQ_NUM_compute] \\ rw []
    \\ fs [c_pushes_def] \\ rw [] \\ fs [flatten_def]
    \\ qexists_tac ‘[Word h''''; Word h'''; Word h''; Word h'; Word h]’ \\ fs []
    \\ fs [code_in_def,pops_regs_def,ZIP_def,write_regs_def]
    \\ ho_match_mp_tac IMP_steps_alt
    \\ ntac 4 (ho_match_mp_tac IMP_step \\ fs []
               \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
               \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,EVEN]
               \\ fs [GSYM PULL_EXISTS])
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘State t1’
    \\ qexists_tac ‘t1’
    \\ fs [Abbr‘t1’,has_stack_def,APPLY_UPDATE_THM]
    \\ fs [state_rel_def,APPLY_UPDATE_THM]
    \\ fs [env_ok_def,make_env_def,empty_env_def,APPLY_UPDATE_THM]
    \\ rw [] \\ EVAL_TAC \\ fs [])
  \\ rw [] \\ fs [LENGTH_EQ_NUM_compute] \\ rw []
QED

Theorem lookup_thm:
  ∀fs t pos. ALOOKUP fs t = SOME pos ⇒ lookup t fs = pos
Proof
  Induct \\ fs [FORALL_PROD,AllCaseEqs(),lookup_def] \\ rw []
  \\ res_tac \\ fs []
QED

Theorem pops_regs:
  pops_regs ws regs RAX = regs RAX ∧
  pops_regs ws regs R12 = regs R12 ∧
  pops_regs ws regs R13 = regs R13 ∧
  pops_regs ws regs R14 = regs R14 ∧
  pops_regs ws regs R15 = regs R15
Proof
  fs [pops_regs_def] \\ IF_CASES_TAC \\ fs [] \\ Cases_on ‘ws’ \\ fs []
  \\ rpt (rename [‘LENGTH tt’] \\ Cases_on ‘tt’  \\ fs [ZIP_def] THEN1 EVAL_TAC)
QED

Theorem c_exp_Call_tail:
  ^Call_tail
Proof
  rw [] \\ fs [eval_def]
  \\ Cases_on ‘evals env xs s’ \\ fs []
  \\ Cases_on ‘q = Err Crash’ \\ fs []
  \\ fs [c_exp_alt]
  \\ Cases_on ‘c_exps t'.pc vs fs xs’ \\ fs []
  \\ fs [c_call_def] \\ rw []
  \\ fs [flatten_def]
  \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
  \\ once_rewrite_tac [flatten_acc] \\ fs [code_in_def]
  \\ strip_tac
  \\ first_x_assum drule_all
  \\ strip_tac
  \\ Cases_on ‘outcome’
  \\ rename [‘steps (State t',s.clock) (ss,n)’]
  \\ reverse (Cases_on ‘ss’) \\ fs []
  THEN1
   (goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
    \\ fs [AllCaseEqs(),get_env_and_body_def,fail_def,return_def]
    \\ rw [] \\ imp_res_tac eval_mono \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS)
  \\ reverse (Cases_on ‘q’) \\ fs []
  THEN1 (goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [] \\ rw [])
  \\ rw []
  \\ Cases_on ‘get_env_and_body t a r’ \\ fs []
  \\ reverse (Cases_on ‘q’)
  THEN1
   (fs [] \\ rw [] \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [get_env_and_body_def,AllCaseEqs(),fail_def] \\ rw [])
  \\ fs [AllCaseEqs()] \\ rw []
  \\ fs [AllCaseEqs(),get_env_and_body_def,fail_def] \\ rw []
  \\ rfs []
  \\ rename [‘steps (State t1,s.clock) (State t2,r.clock)’]
  \\ ho_match_mp_tac IMP_steps
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ rename [‘evals env xs s = (Res args,r)’]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule (GEN_ALL c_pops_thm)
  \\ imp_res_tac steps_inst \\ fs []
  \\ imp_res_tac c_exp_length \\ fs []
  \\ disch_then drule
  \\ ‘∃r15. t2.regs R15 = SOME r15’ by fs [state_rel_def] \\ fs []
  \\ pop_assum kall_tac
  \\ disch_then (qspecl_then [‘r.clock’,‘fs’,‘r.funs’] mp_tac)
  \\ impl_tac
  THEN1
   (imp_res_tac LIST_REL_LENGTH
    \\ imp_res_tac evals_length \\ fs []
    \\ fs [state_rel_def,ODD_ADD,env_ok_def,EVEN_ODD])
  \\ strip_tac
  \\ ho_match_mp_tac IMP_steps
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ Cases_on ‘outcome’ \\ fs []
  \\ reverse (Cases_on ‘q’) \\ fs [] \\ rw []
  THEN1
   (ho_match_mp_tac IMP_start \\ fs []
    \\ imp_res_tac eval_mono \\ fs [state_rel_def] \\ rfs [])
  \\ ho_match_mp_tac IMP_step \\ fs []
  \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
  \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,EVEN]
  \\ CONV_TAC (RESORT_EXISTS_CONV rev) \\ rfs []
  \\ qexists_tac ‘rest’
  \\ qexists_tac ‘curr’ \\ fs []
  \\ ‘LENGTH vs = LENGTH curr’ by fs [env_ok_def] \\ fs []
  \\ Cases_on ‘r.clock’ \\ fs []
  \\ ho_match_mp_tac IMP_step'
  \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
  \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,EVEN,
         take_branch_cases,set_pc_def]
  \\ fs [env_and_body_def,fail_def,AllCaseEqs()] \\ rw []
  \\ ‘code_rel fs r.funs t2.instructions’ by fs [state_rel_def]
  \\ fs [code_rel_def]
  \\ first_x_assum drule
  \\ strip_tac \\ fs [name_of_def]
  \\ imp_res_tac lookup_thm \\ fs []
  \\ fs [c_defun_def]
  \\ rpt (pairarg_tac \\ fs [flatten_def])
  \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
  \\ once_rewrite_tac [flatten_acc]
  \\ fs [code_in_def] \\ rw []
  \\ qmatch_goalsub_abbrev_tac ‘State t3’
  \\ drule c_pushes_thm
  \\ ‘t1.instructions = t3.instructions’ by fs [Abbr‘t3’] \\ fs []
  \\ ‘code_in t3.pc (flatten c0 []) t3.instructions’ by fs [Abbr‘t3’]
  \\ disch_then drule
  \\ ‘t3.regs = pops_regs ws t2.regs’ by fs [Abbr‘t3’]
  \\ disch_then drule
  \\ ‘LIST_REL (v_inv t3) args ws’ by
    (first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
     \\ fs [Abbr‘t3’])
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ ‘∃w'. t3.regs RAX = SOME w'’ by
       rfs [has_stack_def,Abbr‘t3’,pops_regs]
  \\ fs []
  \\ disch_then (qspecl_then [‘r’,‘n’,‘fs’] mp_tac)
  \\ impl_tac
  THEN1 (imp_res_tac LIST_REL_LENGTH \\ fs []
         \\ fs [state_rel_def,Abbr‘t3’,pops_regs]
         \\ rfs [has_stack_def]
         \\ Cases_on ‘ws = []’ \\ fs []
         \\ ‘∃x l. ws = SNOC x l’ by metis_tac [SNOC_CASES] \\ fs [])
  \\ strip_tac
  \\ ho_match_mp_tac IMP_steps
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [Abbr‘t3’]
  \\ qpat_x_assum ‘t5.pc = _’ (assume_tac o GSYM)  \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ disch_then match_mp_tac \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ fs [state_rel_def]
QED

Theorem c_exp_Call_not_tail:
  ^Call_not_tail
Proof
  rw [] \\ fs [eval_def]
  \\ Cases_on ‘evals env xs s’ \\ fs []
  \\ Cases_on ‘q = Err Crash’ \\ fs []
  \\ fs [c_exp_alt]
  \\ Cases_on ‘c_exps t'.pc vs fs xs’ \\ fs []
  \\ fs [c_call_def] \\ rw []
  \\ fs [flatten_def]
  \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
  \\ once_rewrite_tac [flatten_acc] \\ fs [code_in_def]
  \\ strip_tac
  \\ first_x_assum drule_all
  \\ strip_tac
  \\ Cases_on ‘outcome’
  \\ rename [‘steps (State t',s.clock) (ss,n)’]
  \\ reverse (Cases_on ‘ss’) \\ fs []
  THEN1
   (goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
    \\ fs [AllCaseEqs(),get_env_and_body_def,fail_def,return_def]
    \\ rw [] \\ imp_res_tac eval_mono \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS)
  \\ reverse (Cases_on ‘q’) \\ fs []
  THEN1 (goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [] \\ rw [])
  \\ rw []
  \\ Cases_on ‘get_env_and_body t a r’ \\ fs []
  \\ reverse (Cases_on ‘q’)
  THEN1
   (fs [] \\ rw [] \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [get_env_and_body_def,AllCaseEqs(),fail_def] \\ rw [])
  \\ fs [AllCaseEqs()] \\ rw []
  \\ fs [AllCaseEqs(),get_env_and_body_def,fail_def] \\ rw []
  \\ rfs []
  \\ rename [‘steps (State t1,s.clock) (State t2,r.clock)’]
  \\ ho_match_mp_tac IMP_steps
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ rename [‘evals env xs s = (Res args,r)’]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule (GEN_ALL c_pops_thm)
  \\ imp_res_tac steps_inst \\ fs []
  \\ imp_res_tac c_exp_length \\ fs []
  \\ disch_then drule
  \\ ‘∃r15. t2.regs R15 = SOME r15’ by fs [state_rel_def] \\ fs []
  \\ pop_assum kall_tac
  \\ disch_then (qspecl_then [‘r.clock’,‘fs’,‘r.funs’] mp_tac)
  \\ impl_tac
  THEN1
   (imp_res_tac LIST_REL_LENGTH
    \\ imp_res_tac evals_length \\ fs []
    \\ fs [state_rel_def,ODD_ADD,env_ok_def,EVEN_ODD])
  \\ strip_tac
  \\ ho_match_mp_tac IMP_steps
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ Cases_on ‘outcome’ \\ fs []
  \\ reverse (Cases_on ‘q’) \\ fs [] \\ rw []
  THEN1
   (ho_match_mp_tac IMP_start \\ fs []
    \\ imp_res_tac eval_mono \\ fs [state_rel_def] \\ rfs [])
  \\ reverse (Cases_on ‘EVEN (LENGTH vs)’) \\ fs [align_def,code_in_def]
  THEN1
   (Cases_on ‘r.clock’ \\ fs []
    \\ ho_match_mp_tac IMP_step' \\ fs []
    \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
    \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,EVEN,set_pc_def]
    \\ qmatch_goalsub_abbrev_tac ‘State t4’
    \\ fs [env_and_body_def,fail_def,AllCaseEqs()] \\ rw []
    \\ ‘code_rel fs r.funs t4.instructions’ by fs [state_rel_def,Abbr‘t4’]
    \\ fs [code_rel_def]
    \\ first_x_assum drule
    \\ strip_tac \\ fs [name_of_def]
    \\ imp_res_tac lookup_thm \\ fs []
    \\ fs [c_defun_def]
    \\ rpt (pairarg_tac \\ fs [flatten_def])
    \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
    \\ once_rewrite_tac [flatten_acc]
    \\ fs [code_in_def] \\ rw []
    \\ drule c_pushes_thm
    \\ ‘t1.instructions = t4.instructions’ by fs [Abbr‘t4’] \\ fs []
    \\ ‘code_in t4.pc (flatten c0 []) t4.instructions’ by fs [Abbr‘t4’]
    \\ disch_then drule
    \\ ‘t4.regs = pops_regs ws t2.regs’ by fs [Abbr‘t4’]
    \\ disch_then drule
    \\ ‘LIST_REL (v_inv t4) args ws’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
       \\ fs [Abbr‘t4’])
    \\ disch_then (first_assum o mp_then Any mp_tac)
    \\ ‘∃w'. t4.regs RAX = SOME w'’ by
         rfs [has_stack_def,Abbr‘t4’,pops_regs]
    \\ fs []
    \\ disch_then (qspecl_then [‘r’,‘n’,‘fs’] mp_tac)
    \\ impl_tac
    THEN1 (imp_res_tac LIST_REL_LENGTH \\ fs []
           \\ fs [state_rel_def,Abbr‘t4’,pops_regs]
           \\ rfs [has_stack_def]
           \\ Cases_on ‘ws = []’ \\ fs []
           \\ ‘∃x l. ws = SNOC x l’ by metis_tac [SNOC_CASES] \\ fs [])
    \\ strip_tac
    \\ ho_match_mp_tac IMP_steps
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [Abbr‘t4’]
    \\ qpat_x_assum ‘t5.pc = _’ (assume_tac o GSYM)  \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ disch_then (first_assum o mp_then (Pos (el 3)) mp_tac)
    \\ impl_tac
    THEN1 (rfs [ODD,ODD_ADD,EVEN_ODD,env_ok_def] \\ fs [state_rel_def])
    \\ strip_tac \\ PairCases_on‘outcome’
    \\ reverse (Cases_on ‘outcome0’) \\ fs [] \\ rw []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ reverse (Cases_on ‘res’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ ho_match_mp_tac IMP_steps
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ step_tac
    \\ fs [PULL_EXISTS,has_stack_def]
    \\ qpat_x_assum ‘_ = _.stack’ (assume_tac o GSYM) \\ fs []
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ fs [state_rel_def])
  THEN1
   (Cases_on ‘r.clock’ \\ fs []
    \\ ho_match_mp_tac IMP_step \\ fs []
    \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
    \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,
           EVEN,set_pc_def,fetch_def,pops_regs]
    \\ ‘∃rax. t2.regs RAX = SOME rax’ by fs [has_stack_def] \\ fs []
    \\ pop_assum kall_tac
    \\ ho_match_mp_tac IMP_step' \\ fs []
    \\ once_rewrite_tac [step_cases] \\ fs [fetch_def,PULL_EXISTS]
    \\ fs [write_reg_def,set_stack_def,inc_def,APPLY_UPDATE_THM,EVEN,set_pc_def]
    \\ qmatch_goalsub_abbrev_tac ‘State t4’
    \\ fs [env_and_body_def,fail_def,AllCaseEqs()] \\ rw []
    \\ ‘code_rel fs r.funs t4.instructions’ by fs [state_rel_def,Abbr‘t4’]
    \\ fs [code_rel_def]
    \\ first_x_assum drule
    \\ strip_tac \\ fs [name_of_def]
    \\ imp_res_tac lookup_thm \\ fs []
    \\ fs [c_defun_def]
    \\ rpt (pairarg_tac \\ fs [flatten_def])
    \\ qpat_x_assum ‘code_in _ _ _’ mp_tac
    \\ once_rewrite_tac [flatten_acc]
    \\ fs [code_in_def] \\ rw []
    \\ drule c_pushes_thm
    \\ ‘t1.instructions = t4.instructions’ by fs [Abbr‘t4’] \\ fs []
    \\ ‘code_in t4.pc (flatten c0 []) t4.instructions’ by fs [Abbr‘t4’]
    \\ disch_then drule
    \\ ‘t4.regs = pops_regs ws t2.regs’ by fs [Abbr‘t4’]
    \\ disch_then drule
    \\ ‘LIST_REL (v_inv t4) args ws’ by
      (first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
       \\ fs [Abbr‘t4’])
    \\ disch_then (first_assum o mp_then Any mp_tac)
    \\ ‘∃w'. t4.regs RAX = SOME w'’ by
         rfs [has_stack_def,Abbr‘t4’,pops_regs]
    \\ fs []
    \\ disch_then (qspecl_then [‘r’,‘n’,‘fs’] mp_tac)
    \\ impl_tac
    THEN1 (imp_res_tac LIST_REL_LENGTH \\ fs []
           \\ fs [state_rel_def,Abbr‘t4’,pops_regs]
           \\ rfs [has_stack_def]
           \\ Cases_on ‘ws = []’ \\ fs []
           \\ ‘∃x l. ws = SNOC x l’ by metis_tac [SNOC_CASES] \\ fs [])
    \\ strip_tac
    \\ ho_match_mp_tac IMP_steps
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [Abbr‘t4’]
    \\ qpat_x_assum ‘t5.pc = _’ (assume_tac o GSYM)  \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ disch_then (first_assum o mp_then (Pos (el 3)) mp_tac)
    \\ impl_tac
    THEN1 (rfs [ODD,ODD_ADD,EVEN_ODD,env_ok_def] \\ fs [state_rel_def])
    \\ strip_tac \\ PairCases_on‘outcome’
    \\ reverse (Cases_on ‘outcome0’) \\ fs [] \\ rw []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ reverse (Cases_on ‘res’) \\ fs []
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ ho_match_mp_tac IMP_steps
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ step_tac
    \\ fs [PULL_EXISTS,has_stack_def]
    \\ qpat_x_assum ‘_ = _.stack’ (assume_tac o GSYM) \\ fs []
    \\ imp_res_tac steps_inst \\ fs []
    \\ step_tac
    \\ ho_match_mp_tac IMP_start \\ fs []
    \\ fs [state_rel_def,APPLY_UPDATE_THM])
QED

Theorem c_exp_Call:
  ^(get_goal "eval _ (Call _ _)")
Proof
  Call_init_tac \\ rewrite_tac [c_exp_Call_tail,c_exp_Call_not_tail]
QED

Theorem c_exps_nil:
  ^(get_goal "evals _ []")
Proof
  fs [eval_def,c_exp_alt] \\ rw []
  \\ qexists_tac ‘State t, s.clock’ \\ fs []
  \\ simp [Once steps_cases]
QED

Theorem c_exps_cons:
  ^(get_goal "evals _ (_::_)")
Proof
  fs [eval_def,c_exp_alt] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt var_eq_tac
  \\ Cases_on ‘eval env x s’ \\ fs []
  \\ Cases_on ‘q = Err Crash’ \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ rpt (disch_then drule)
  \\ impl_tac THEN1
   (qpat_x_assum ‘code_in _ _ _’ mp_tac
    \\ fs [flatten_def] \\ simp [Once flatten_acc])
  \\ strip_tac
  \\ Cases_on ‘outcome’
  \\ rename [‘steps _ (r1,r2)’]
  \\ reverse (Cases_on ‘r1’) \\ fs []
  THEN1
   (goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ fs [AllCaseEqs()] \\ rw []
    \\ imp_res_tac eval_mono
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS)
  \\ reverse (Cases_on ‘q’) \\ fs []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [] \\ rw [])
  \\ Cases_on ‘evals env xs r’ \\ fs []
  \\ Cases_on ‘q = Err Crash’ \\ fs [] \\ rw []
  \\ first_x_assum drule \\ fs []
  \\ disch_then (qspecl_then [‘Word w :: curr’,‘rest’] mp_tac)
  \\ impl_tac THEN1
   (qpat_x_assum ‘code_in _ _ _’ mp_tac
    \\ fs [flatten_def] \\ simp [Once flatten_acc]
    \\ imp_res_tac c_exp_length \\ fs []
    \\ imp_res_tac steps_inst \\ fs [] \\ rw []
    \\ fs [env_ok_def] \\ rw []
    \\ first_x_assum drule
    \\ rw [] \\ fs [find_def]
    \\ once_rewrite_tac [find_acc] \\ fs [ADD1]
    \\ fs [GSYM ADD1]
    \\ imp_res_tac steps_v_inv \\ fs [])
  \\ strip_tac
  \\ qexists_tac ‘outcome’
  \\ conj_tac THEN1 (Cases_on ‘outcome’ \\ imp_res_tac steps_rules \\ fs [])
  \\ Cases_on ‘outcome’
  \\ fs [AllCaseEqs()] \\ rw []
  \\ Cases_on ‘q'’ \\ fs []
  \\ imp_res_tac eval_mono
  \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ fs [PULL_EXISTS]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
  \\ imp_res_tac steps_v_inv \\ fs []
QED


(* putting all the cases together *)

Theorem c_exp_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [c_exp_Const, c_exp_Var,
      c_exp_Op, c_exp_If, c_exp_Let, c_exp_Call, c_exps_nil, c_exps_cons])
  \\ asm_rewrite_tac []
QED

Theorem c_exp_Evals:
  (env,[x],s) ---> ([v],s1) ∧
  c_exp is_tail t.pc vs fs x = (code,l1) ∧ state_rel fs s t ∧
  env_ok env vs curr t ∧ has_stack t (curr ⧺ rest) ∧
  ODD (LENGTH rest) ∧ code_in t.pc (flatten code []) t.instructions ⇒
  ∃outcome.
    RTC step (State t) outcome ∧
    case outcome of
    | (Halt ec output) => output ≼ s1.output ∧ ec = 1w
    | (State t1) =>
        state_rel fs s1 t1 ∧
        ∃w. v_inv t1 v w ∧
            if is_tail then
              has_stack t1 (Word w::rest) ∧ fetch t1 = SOME Ret
            else
              has_stack t1 (Word w::curr ++ rest) ∧ t1.pc = l1
Proof
  rw [] \\ drule Eval_imp_evals \\ strip_tac
  \\ fs [eval_def,AllCaseEqs()]
  \\ drule (CONJUNCT1 c_exp_correct) \\ fs []
  \\ disch_then drule \\ fs []
  \\ disch_then (qspecl_then [‘curr’,‘rest’] mp_tac)
  \\ impl_tac THEN1 fs [state_rel_def]
  \\ strip_tac
  \\ PairCases_on ‘outcome’ \\ fs []
  \\ qexists_tac ‘outcome0’ \\ fs []
  \\ imp_res_tac steps_imp_RTC_step \\ fs []
  \\ TOP_CASE_TAC \\ fs [] \\ qexists_tac ‘w’ \\ fs []
  \\ TOP_CASE_TAC \\ fs []
QED

(* compilation of enitre program *)

Triviality FST_SND:
  FST = (λ(x,y). x) ∧ SND = (λ(x,y). y)
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem c_decs_append:
  ∀xs ys l fs fs' l' c.
    c_decs l fs (xs ++ ys) = (c,fs',l') ⇒
      let (c1,fs1,l1) = c_decs l fs xs in
      let (c2,fs2,l2) = c_decs l1 fs ys in
        l' = l2 ∧
        fs' = fs1 ++ fs2 ∧
        flatten c [] = flatten (Append c1 c2) []
Proof
  Induct \\ fs [c_decs_def]
  THEN1 fs [flatten_def]
  \\ rw [] \\ fs [FST_SND] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt var_eq_tac \\ fs []
  \\ first_x_assum drule
  \\ fs [] \\ strip_tac
  \\ rpt var_eq_tac \\ fs []
  \\ fs [flatten_def]
QED

Theorem c_exp_11:
  (∀t l vs fs1 e fs2 c1 l1 c2 l2.
     c_exp t l vs fs1 e = (c1,l1) ∧
     c_exp t l vs fs2 e = (c2,l2) ⇒ l1 = l2) ∧
  (∀l vs fs1 e fs2 c1 l1 c2 l2.
     c_exps l vs fs1 e = (c1,l1) ∧
     c_exps l vs fs2 e = (c2,l2) ⇒ l1 = l2)
Proof
  ho_match_mp_tac c_exp_ind_alt \\ rw []
  \\ fs [c_exp_alt,c_if_def,c_call_def,make_ret_def]
  \\ rpt (pairarg_tac \\ fs []) \\ fs [make_ret_def]
  \\ rpt var_eq_tac \\ fs []
  \\ res_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ fs [make_ret_def]
  \\ rpt var_eq_tac \\ fs []
  \\ res_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ fs [make_ret_def]
  \\ rpt var_eq_tac \\ fs []
  \\ res_tac \\ fs []
  THEN1
   (Cases_on ‘c_exps l vs fs1 e’ \\ Cases_on ‘c_exps l vs fs2 e’ \\ fs []
    \\ res_tac \\ fs [] \\ fs [c_call_def,AllCaseEqs()]
    \\ rpt var_eq_tac \\ fs []
    \\ res_tac \\ fs [align_def] \\ rw [] \\ fs [])
  \\ first_assum (qspec_then ‘fs1’ mp_tac) \\ fs []
  \\ first_x_assum (qspec_then ‘fs2’ mp_tac) \\ fs []
QED

Theorem c_defun_length_11:
  c_defun l fs1 d = (c1,l1) ∧ c_defun l fs2 d = (c2,l2) ⇒ l1 = l2
Proof
  Cases_on ‘d’ \\ fs [c_defun_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ imp_res_tac c_exp_11 \\ fs []
QED

Theorem c_decs_length_11:
  ∀l fs1 fs2 ds c1 c2 fs'1 l1 fs'2 l2.
    c_decs l fs1 ds = (c1,fs'1,l1) ∧
    c_decs l fs2 ds = (c2,fs'2,l2) ⇒
    l1 = l2 ∧ fs'1 = fs'2
Proof
  Induct_on ‘ds’ \\ fs [c_decs_def]
  \\ rpt gen_tac \\ strip_tac
  \\ qabbrev_tac ‘p1 = c_defun (l + 1) fs1 h’
  \\ qabbrev_tac ‘p2 = c_defun (l + 1) fs2 h’
  \\ qabbrev_tac ‘q1 = c_decs (SND p1) fs1 ds’
  \\ qabbrev_tac ‘q2 = c_decs (SND p2) fs2 ds’
  \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ fs []
  \\ PairCases_on ‘q1’ \\ PairCases_on ‘q2’ \\ fs []
  \\ fs [markerTheory.Abbrev_def]
  \\ metis_tac [c_defun_length_11]
QED

Theorem c_defun_length:
  c_defun l fs d = (c1,l1) ⇒ l1 = LENGTH (flatten c1 []) + l
Proof
  Cases_on ‘d’ \\ fs [c_defun_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [flatten_def] \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ imp_res_tac c_exp_length \\ fs [] \\ rw []
  \\ fs [c_pushes_def,AllCaseEqs()]
  \\ rw [] \\ fs [flatten_def]
QED

Theorem c_decs_length:
  ∀ds l fs c1 fs1 l1.
    c_decs l fs ds = (c1,fs1,l1) ⇒ l1 = LENGTH (flatten c1 []) + l
Proof
  Induct \\ fs [c_decs_def] \\ fs [flatten_def] \\ rw []
  \\ Cases_on ‘c_defun (l + 1) fs h’ \\ fs []
  \\ Cases_on ‘c_decs r fs ds’ \\ fs [] \\ PairCases_on ‘r'’ \\ fs []
  \\ res_tac \\ fs []
  \\ imp_res_tac c_defun_length \\ rw [] \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs []
QED

Theorem lookup_LENGTH:
  ∀xs h ys. lookup (LENGTH xs) (xs ⧺ h::ys) = SOME h
Proof
  Induct \\ fs [x64asm_semanticsTheory.lookup_def]
QED

Theorem IMP_code_in_append:
  ∀xs ys k. k = LENGTH xs ⇒ code_in k ys (xs ++ ys)
Proof
  Induct_on ‘ys’ \\ fs [code_in_def,lookup_LENGTH] \\ rw []
  \\ first_x_assum (qspec_then ‘xs ++ [h]’ mp_tac)
  \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] \\ fs []
QED

Theorem IMP_code_in_append2:
  ∀xs ys zs k. k = LENGTH xs ⇒ code_in k ys (xs ++ ys ++ zs)
Proof
  Induct_on ‘ys’ \\ fs [code_in_def,lookup_LENGTH] \\ rw []
  \\ first_x_assum (qspec_then ‘xs ++ [h]’ mp_tac)
  \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [lookup_LENGTH]
QED

Theorem c_decs_code_in:
  ∀ds l fs0 fs c1 k n params body xs acc.
    c_decs l fs0 ds = (c1,fs,k) ∧
    lookup_fun n ds = SOME (params,body) ∧
    LENGTH xs = l ⇒
    ∃pos.
      ALOOKUP fs n = SOME pos ∧
      code_in pos (flatten (FST (c_defun pos fs0 (Defun n params body))) [])
        (xs ⧺ flatten c1 acc)
Proof
  Induct \\ fs [c_decs_def,lookup_fun_def] \\ rw []
  \\ Cases_on ‘c_defun (LENGTH xs + 1) fs0 h’ \\ fs []
  \\ Cases_on ‘c_decs r fs0 ds’ \\ fs []
  \\ rpt var_eq_tac
  \\ Cases_on ‘h’ \\ fs []
  \\ fs [lookup_fun_def,name_of_def]
  \\ rw []
  \\ rw [] \\ imp_res_tac c_defun_length \\ fs [] \\ rw []
  \\ fs [flatten_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def,code_in_def]
  \\ once_rewrite_tac [flatten_acc] \\ fs [flatten_def,code_in_def]
  THEN1
   (rename [‘xs ++ x::(ys ++ zs ++ acc)’]
    \\ ‘xs ⧺ x::(ys ⧺ zs ++ acc) = (xs ⧺ [x]) ++ ys ⧺ (zs ++ acc)’ by fs []
    \\ asm_rewrite_tac []
    \\ match_mp_tac IMP_code_in_append2 \\ fs [])
  \\ qmatch_asmsub_abbrev_tac ‘c_decs pos1’ \\ rfs []
  \\ rename [‘xs ++ x::(ys ++ _ ++ acc)’]
  \\ ‘xs ⧺ x::(ys ⧺ flatten q' [] ⧺ acc) = (xs ⧺ x::ys) ⧺ flatten q' acc’
         by fs [GSYM flatten_acc]
  \\ asm_rewrite_tac []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ unabbrev_all_tac \\ fs [ADD1]
  \\ Cases_on ‘r'’ \\ fs []
QED

Theorem codegen_thm:
  eval empty_env main s = (res,s1) ∧ res ≠ Err Crash ∧
  s.funs = funs ∧
  t.pc = 0 ∧
  t.instructions = codegen (Program funs main) ∧
  t.stack = [] ∧
  t.input = s.input ∧
  t.output = s.output ∧
  t.regs R14 = SOME r14 ∧
  t.regs R15 = SOME r15 ∧
  memory_writable r14 r15 t.memory ⇒
  ∃outcome.
    steps (State t,s.clock) outcome ∧
    case outcome of
    | (State t1,ck) => t1.output = s1.output ∧ ck = s1.clock ∧ res = Err TimeOut
    | (Halt ec output,ck) => if ec ≠ 0w then output ≼ s1.output
                                        else output = s1.output ∧ ∃v. res = Res v
Proof
  rw [] \\ fs [codegen_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ qpat_x_assum ‘t.instructions = _’ mp_tac
  \\ simp [flatten_def] \\ once_rewrite_tac [flatten_acc] \\ fs []
  \\ rw [] \\ fs []
  \\ ntac 4 (ho_match_mp_tac IMP_step \\ fs []
             \\ once_rewrite_tac [step_cases]
             \\ simp [fetch_def,init_def,x64asm_semanticsTheory.lookup_def]
             \\ fs [write_reg_def,inc_def,APPLY_UPDATE_THM,
                    set_pc_def,set_stack_def,LENGTH_EQ_NUM_compute])
  \\ qmatch_goalsub_abbrev_tac ‘State t2’
  \\ ‘code_in t2.pc (flatten (FST (c_defun t2.pc fs (Defun (name "main") [] main))) [])
        t.instructions’ by
   (drule c_decs_append \\ fs []
    \\ rpt (pairarg_tac \\ fs []) \\ rw [] \\ fs [c_decs_def]
    \\ imp_res_tac c_decs_length_11 \\ rpt var_eq_tac
    \\ qmatch_goalsub_abbrev_tac ‘FST ff’
    \\ ‘t2.pc = k + 1’ by fs [Abbr‘t2’] \\ fs []
    \\ PairCases_on ‘ff’ \\ fs [] \\ rpt var_eq_tac
    \\ qmatch_asmsub_abbrev_tac ‘Comment com’ \\ fs [flatten_def]
    \\ once_rewrite_tac [flatten_acc] \\ fs [code_in_def]
    \\ imp_res_tac c_decs_length \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘init kk ++ flatten c1 [] ++ cc::_’
    \\ ‘init kk ⧺ flatten c1 [] ⧺ cc::flatten ff0 [] =
        (init kk ⧺ flatten c1 [] ⧺ [cc]) ++ flatten ff0 []’ by fs []
    \\ pop_assum (asm_rewrite_tac o single)
    \\ match_mp_tac IMP_code_in_append
    \\ fs [Abbr‘kk’] \\ EVAL_TAC)
  \\ fs [c_defun_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [c_pushes_def] \\ rw []
  \\ fs [flatten_def]
  \\ drule (c_exp_correct |> CONJUNCT1) \\ fs []
  \\ disch_then drule
  \\ disch_then (qspecl_then [‘[Word 0w]’,‘[RetAddr 4]’] mp_tac)
  \\ impl_tac THEN1
   (fs [has_stack_def,Abbr‘t2’] \\ rfs [APPLY_UPDATE_THM]
    \\ fs [env_ok_def,empty_env_def,state_rel_def,APPLY_UPDATE_THM]
    \\ fs [code_rel_def,init_code_in_def]
    \\ conj_tac THEN1 (qexists_tac ‘k+1’ \\ fs [] \\ EVAL_TAC)
    \\ imp_res_tac c_decs_append \\ rfs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ imp_res_tac c_decs_length_11 \\ rpt var_eq_tac
    \\ pop_assum kall_tac \\ rw []
    \\ ‘LENGTH (init (k+1)) = LENGTH (init 0)’ by EVAL_TAC
    \\ drule_all c_decs_code_in \\ fs [flatten_def])
  \\ strip_tac
  \\ PairCases_on ‘outcome’ \\ reverse (Cases_on ‘outcome0’) \\ fs []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ reverse (Cases_on ‘res’) \\ fs []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac)
         \\ fs [state_rel_def] \\ Cases_on ‘e’ \\ fs [])
  \\ ho_match_mp_tac IMP_steps \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [fetch_def,has_stack_def]
  \\ ho_match_mp_tac IMP_step \\ fs []
  \\ once_rewrite_tac [step_cases]
  \\ simp [fetch_def,init_def,x64asm_semanticsTheory.lookup_def]
  \\ fs [write_reg_def,inc_def,APPLY_UPDATE_THM,
         set_pc_def,set_stack_def,LENGTH_EQ_NUM_compute,PULL_EXISTS]
  \\ imp_res_tac steps_inst \\ fs [Abbr‘t2’]
  \\ ntac 2 (ho_match_mp_tac IMP_step \\ fs []
             \\ once_rewrite_tac [step_cases]
             \\ simp [fetch_def,init_def,x64asm_semanticsTheory.lookup_def]
             \\ fs [write_reg_def,inc_def,APPLY_UPDATE_THM,
                    set_pc_def,set_stack_def,LENGTH_EQ_NUM_compute])
  \\ ho_match_mp_tac IMP_start \\ fs []
  \\ fs [state_rel_def]
QED

Theorem codegen_terminates:
  (input, prog) prog_terminates output1 ∧
  (input, codegen prog) asm_terminates output2 ⇒
  output1 = output2
Proof
  Cases_on ‘prog’
  \\ rw [prog_terminates_def,asm_terminates_def,Eval_eq_evals,init_state_ok_def]
  \\ fs [eval_def,AllCaseEqs()]
  \\ drule codegen_thm \\ fs []
  \\ disch_then drule \\ fs []
  \\ fs [init_state_def] \\ rw []
  \\ PairCases_on ‘outcome’ \\ fs []
  \\ Cases_on ‘outcome0’ \\ fs []
  \\ imp_res_tac steps_imp_RTC_step \\ fs []
  \\ imp_res_tac RTC_step_determ \\ fs []
QED

Theorem codegen_diverges:
  prog_avoids_crash input prog ∧
  (input, codegen prog) asm_diverges output ⇒
  (input, prog) prog_diverges output
Proof
  rw [prog_avoids_crash_def,asm_diverges_def,prog_diverges_def,init_state_ok_def]
  THEN1
   (CCONTR_TAC \\ fs [prog_timesout_def]
    \\ last_x_assum (qspec_then ‘k’ assume_tac)
    \\ Cases_on ‘eval_from k t.input prog’ \\ fs []
    \\ reverse (Cases_on ‘q’)
    THEN1 (Cases_on ‘e’ \\ fs [] \\ rw [] \\ fs []) \\ fs []
    \\ rw [] \\ Cases_on ‘prog’ \\ fs [eval_from_def]
    \\ drule codegen_thm \\ fs []
    \\ fs [init_state_def]
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ Cases_on ‘outcome’ \\ fs []
    \\ Cases_on ‘q’ \\ fs []
    \\ drule steps_IMP_NRC_step \\ strip_tac
    \\ rename [‘NRC _ kk’]
    \\ first_x_assum (qspec_then ‘kk’ mp_tac) \\ strip_tac
    \\ imp_res_tac NRC_step_determ \\ fs [])
  \\ match_mp_tac IMP_build_lprefix_lub_EQ
  \\ rewrite_tac [lprefix_chain_step]
  \\ conj_asm1_tac THEN1
   (unabbrev_all_tac
    \\ fs [lprefix_chain_def,prog_output_def,PULL_EXISTS]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ fs [llistTheory.LPREFIX_fromList,llistTheory.from_toList]
    \\ rpt gen_tac
    \\ ‘k ≤ k' ∨ k' ≤ k’ by fs []
    \\ Cases_on ‘eval_from k t.input prog’ \\ fs []
    \\ Cases_on ‘eval_from k' t.input prog’ \\ fs []
    \\ imp_res_tac eval_from_prefix \\ fs [])
  \\ rw [lprefix_rel_def] \\ fs [PULL_EXISTS]
  THEN1
   (imp_res_tac RTC_NRC \\ rename [‘NRC _ kk’] \\ rw []
    \\ qexists_tac ‘kk’ \\ last_x_assum (qspec_then ‘kk’ assume_tac)
    \\ Cases_on ‘eval_from kk t.input prog’ \\ fs []
    \\ Cases_on ‘prog’ \\ fs [eval_from_def,prog_output_def]
    \\ drule codegen_thm \\ fs []
    \\ disch_then drule \\ fs []
    \\ fs [init_state_def] \\ rw []
    \\ PairCases_on ‘outcome’ \\ fs []
    \\ Cases_on ‘outcome0’ \\ fs []
    THEN1
     (imp_res_tac eval_TimeOut_clock \\ rw [] \\ fs []
      \\ imp_res_tac asm_output_PREFIX
      \\ rfs [LPREFIX_fromList,from_toList])
    \\ drule steps_IMP_NRC_step \\ strip_tac
    \\ rename [‘NRC _ kk’]
    \\ first_x_assum (qspec_then ‘kk’ mp_tac) \\ strip_tac
    \\ imp_res_tac NRC_step_determ \\ fs [])
  \\ last_x_assum (qspec_then ‘k’ assume_tac)
  \\ Cases_on ‘eval_from k t.input prog’ \\ fs [LNTH_fromList] \\ rw []
  \\ Cases_on ‘prog’ \\ fs [eval_from_def,prog_output_def]
  \\ drule codegen_thm \\ fs []
  \\ disch_then drule \\ fs []
  \\ fs [init_state_def] \\ rw []
  \\ PairCases_on ‘outcome’ \\ fs []
  \\ Cases_on ‘outcome0’ \\ fs []
  THEN1
   (rw [] \\ qexists_tac ‘s’ \\ fs []
    \\ drule steps_IMP_NRC_step \\ strip_tac
    \\ imp_res_tac NRC_RTC)
  \\ drule steps_IMP_NRC_step \\ strip_tac
  \\ rename [‘NRC _ kk’]
  \\ first_x_assum (qspec_then ‘kk’ mp_tac) \\ strip_tac
  \\ imp_res_tac NRC_step_determ \\ fs []
QED

val _ = export_theory();
