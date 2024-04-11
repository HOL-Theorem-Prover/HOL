
open HolKernel Parse boolLib bossLib term_tactic cv_transLib cv_stdTheory;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open wordsTheory wordsLib printingTheory codegenTheory;

val _ = new_theory "compiler_funs_cv";

(* prepare for fast in-logic evaluation *)

val res = cv_auto_trans codegenTheory.even_len_def;
val res = cv_auto_trans codegenTheory.c_pops_def;

val res = cv_auto_trans_pre_rec codegenTheory.c_exp_def
 (WF_REL_TAC ‘inv_image (measure I LEX measure I)
    (λx. case x of INL (t,l,vs,fs,x) => (cv_size x, cv$c2n t)
                 | INR (l,vs,fs,xs) => (cv_size xs, 0))’
  \\ rpt strip_tac
  \\ (Cases_on ‘cv_z’ ORELSE Cases_on ‘cv_zs’) \\ gvs []
  \\ gvs [cvTheory.c2b_def]
  \\ cv_termination_tac \\ gvs [])

Theorem c_exp_pre[cv_pre]:
  (∀t l vs fs z. c_exp_pre t l vs fs z) ∧
  (∀l vs fs zs. c_exps_pre l vs fs zs)
Proof
  ho_match_mp_tac codegenTheory.c_exp_ind \\ rw [] \\ simp [Once res]
QED

val res = cv_auto_trans_pre printingTheory.is_comment_def;
Theorem is_comment_pre[cv_pre]:
  ∀v. is_comment_pre v
Proof
  ho_match_mp_tac printingTheory.is_comment_ind \\ rw [] \\ simp [Once res]
QED

val pre = cv_trans_pre_rec printingTheory.num2str_def
  (WF_REL_TAC ‘measure cv_size’ \\ Cases \\ gvs [] \\ rw [] \\ gvs []);

Theorem num2str_pre[cv_pre]:
  ∀n. num2str_pre n
Proof
  ho_match_mp_tac printingTheory.num2str_ind \\ rw [] \\ simp [Once pre]
  \\ ‘n MOD 10 < 10’ by fs [] \\ decide_tac
QED

val pre = cv_trans_pre printingTheory.num2ascii_def
Theorem num2ascii_pre[cv_pre]:
  ∀n. num2ascii_pre n
Proof
  ho_match_mp_tac printingTheory.num2ascii_ind \\ rw [] \\ simp [Once pre]
QED

val pre = cv_trans_pre printingTheory.ascii_name_def
Theorem ascii_name_pre[cv_pre]:
  ∀n. ascii_name_pre n
Proof
  simp [Once pre] \\ simp [Once printingTheory.num2ascii_def] \\ rw []
  \\ gvs [AllCaseEqs()]
QED

val pre = cv_trans_pre x64asm_syntaxTheory.num_def;
Theorem num_pre[cv_pre]:
  ∀n s. num_pre n s
Proof
  ho_match_mp_tac x64asm_syntaxTheory.num_ind \\ rw [] \\ simp [Once pre]
  \\ ‘n MOD 10 < 10’ by fs [] \\ decide_tac
QED

Definition vs2pretty_def:
  vs2pretty vs = MAP (λx. v2pretty x) vs
End

Triviality vs2pretty_thm:
  vs2pretty [] = [] ∧
  vs2pretty (v::vs) = v2pretty v :: vs2pretty vs
Proof
  gvs [vs2pretty_def]
QED

val _ = cv_trans printingTheory.dest_list_def;

Theorem cv_dest_list_size:
  ∀v x y.
    cv_dest_list v = Pair x y ⇒
    cv_size x <= cv_size v ∧
    cv_size y <= cv_size v
Proof
  recInduct (fetch "-" "cv_dest_list_ind") \\ rw []
  \\ cv_termination_tac \\ gvs [ADD1]
  \\ pop_assum mp_tac
  \\ simp [Once $ fetch "-" "cv_dest_list_def"] \\ rw [] \\ gvs []
  \\ cv_termination_tac \\ gvs [ADD1]
  \\ Cases_on ‘x2’ \\ gvs []
QED

val v2pretty_eq =
  CONJ (printingTheory.v2pretty_def |> SRULE [GSYM vs2pretty_def]) vs2pretty_thm;

val pre = cv_auto_trans_pre_rec v2pretty_eq
  (WF_REL_TAC ‘measure $ λx. case x of INL v => cv_size v
                                     | INR v => cv_size v’
   \\ rw [] \\ cv_termination_tac
   \\ qpat_x_assum ‘cv_dest_list _ = _’ mp_tac
   \\ simp [Once $ fetch "-" "cv_dest_list_def"] \\ rw [] \\ gvs []
   \\ rw [] \\ cv_termination_tac
   \\ (Cases_on ‘x2’ \\ gvs []
       >- (pop_assum mp_tac
           \\ simp [Once $ fetch "-" "cv_dest_list_def"] \\ rw [] \\ gvs [])
       \\ drule cv_dest_list_size \\ gvs []));

Triviality dest_list_v_size:
  ∀v vs t.
    dest_list v = (vs,t) ⇒
    list_size v_size vs < v_size v ∧
    v_size t ≤ v_size v
Proof
  Induct \\ gvs [printingTheory.dest_list_def,list_size_def]
  \\ rw [] \\ pairarg_tac \\ gvs [] \\ res_tac \\ gvs [list_size_def]
QED

Theorem v2pretty_pre[cv_pre]:
  (∀v. v2pretty_pre v) ∧
  (∀vs. vs2pretty_pre vs)
Proof
  qsuff_tac
     ‘∀n. (∀v. v_size v = n ⇒ v2pretty_pre v) ∧
          (∀vs. list_size v_size vs = n ⇒ vs2pretty_pre vs)’
  >- metis_tac [] \\ gen_tac \\ completeInduct_on ‘n’
  \\ rw [] \\ gvs [SF DNF_ss]
  \\ simp [Once pre] \\ rw []
  \\ first_x_assum irule \\ rw []
  \\ gvs [list_size_def]
  \\ gvs [printingTheory.dest_list_def]
  \\ pairarg_tac \\ gvs [list_size_def]
  \\ imp_res_tac dest_list_v_size \\ gvs []
QED

val res = cv_auto_trans
  (is_protected_def |> SRULE [protected_names_def,source_valuesTheory.name_def]);

Triviality exps2v_eq:
  exps2v [] = [] ∧
  exps2v (x::xs) = exp2v x :: exps2v xs
Proof
  metis_tac [exp2v_def]
QED

val pre = cv_auto_trans_pre_rec exp2v_def
  (WF_REL_TAC ‘measure $ λx. case x of
                             | INL v => cv_size v + 1
                             | INR (INL v) => cv_size v + 1
                             | INR (INR v) => cv_size v’
   \\ cv_termination_tac \\ cheat);

Theorem exp2v_pre[cv_pre]:
  (∀v. exp2v_pre v) ∧
  (∀v. exps2v_pre v) ∧
  (∀v. lets2v_pre v)
Proof
  ho_match_mp_tac printingTheory.exp2v_ind \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs [] \\ gvs [LENGTH_EQ_NUM_compute]
  \\ rpt (qpat_x_assum ‘dest_cons_chain _ = _’ mp_tac
          \\ simp [Once $ oneline dest_cons_chain_def,AllCaseEqs()]
          \\ strip_tac \\ gvs [exps2v_eq])
QED

val res = cv_auto_trans printingTheory.vs2str_def;

val res = cv_auto_trans codegenTheory.codegen_def;
val res = cv_auto_trans x64asm_syntaxTheory.asm2str_def;
val res = cv_auto_trans printingTheory.prog2str_def;

val _ = export_theory();
