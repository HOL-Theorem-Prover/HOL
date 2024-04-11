
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

Triviality cv_EL_trivial:
  ∀n m. cv_EL (Num n) (Num m) = Num 0
Proof
  Induct >> rw[] >> simp[Once cv_EL_def]
QED

Triviality cv_EL_size:
  ∀l n. cv_size (cv_EL n l) ≤ cv_size l
Proof
  Induct >> rw[] >> simp[Once cv_EL_def] >>
  Cases_on `n` >> gvs[] >> IF_CASES_TAC >> gvs[] >>
  pop_assum mp_tac >> IF_CASES_TAC >> gvs[cv_EL_trivial] >>
  irule LESS_EQ_TRANS >> first_x_assum $ irule_at Any >> simp[]
QED

val _ = cv_trans get_Op_Head_def;
val _ = cv_trans dest_case_lets_def;
val _ = cv_trans dest_case_tree_def;
val _ = cv_trans dest_case_enum_def;
val _ = cv_trans dest_cons_chain_def;

Triviality cv_get_Op_Head_size:
  ∀x. cv_size (cv_get_Op_Head x) ≤ cv_size x
Proof
  Induct >> rw[fetch "-" "cv_get_Op_Head_def"] >> cv_termination_tac
QED

Triviality cv_dest_case_lets_size:
  ∀a b x.
    cv_dest_case_lets a b = x
  ⇒ cv_size (cv_snd x) ≤ cv_size b + 3
Proof
  recInduct $ fetch "-" "cv_dest_case_lets_ind" >> rw[] >>
  simp[Once $ fetch "-" "cv_dest_case_lets_def"] >>
  reverse $ rw[] >> gvs[] >> cv_termination_tac >>
  gvs[cvTheory.c2b_def, cvTheory.cv_lt_def0, AllCaseEqs(), cvTheory.b2c_if] >>
  namedCases_on `z` ["", "a1 b1"] >> gvs[] >>
  namedCases_on `b1` ["", "a2 b2"] >> gvs[] >>
  namedCases_on `b2` ["", "a3 b3"] >> gvs[]
QED

Theorem cv_dest_case_tree_size[local]:
  ∀a b x y.
    cv_dest_case_tree a b = Pair x y ⇒
    cv_size (cv_map_snd (cv_map_snd y)) < cv_size b
Proof
  recInduct $ fetch "-" "cv_dest_case_tree_ind" >> rw[] >>
  pop_assum mp_tac >> simp[Once $ fetch "-" "cv_dest_case_tree_def"] >>
  reverse $ rw[] >> gvs[]
  >- (
    simp[SCONV [Once cv_map_snd_def] ``cv_map_snd (Num _)``] >>
    Cases_on `cv_v` >> gvs[]
    ) >>
  simp[SCONV [Once cv_map_snd_def] ``cv_map_snd (Pair _ _)``] >>
  unabbrev_all_tac >> cv_termination_tac >>
  drule cv_dest_case_lets_size >> simp[] >>
  rename1 `cv_dest_case_lets _ (cv_fst x)` >> Cases_on `x` >> gvs[]
QED

Theorem cv_dest_case_enum_size[local]:
  ∀a b x y.
    cv_dest_case_enum a b = Pair x y
  ⇒ cv_size (cv_map_snd y) < cv_size b
Proof
  recInduct $ fetch "-" "cv_dest_case_enum_ind" >> rw[] >>
  pop_assum mp_tac >> simp[Once $ fetch "-" "cv_dest_case_enum_def"] >>
  rw[] >> gvs[] >>
  simp[SCONV [Once cv_map_snd_def] ``cv_map_snd (Num _)``] >>
  simp[SCONV [Once cv_map_snd_def] ``cv_map_snd (Pair _ _)``]
  >- (cv_termination_tac >> rename1 `cv_fst x` >> Cases_on `x` >> gvs[])
  >- (Cases_on `cv_v` >> gvs[])
  >- (cv_termination_tac >> rename1 `cv_fst x` >> Cases_on `x` >> gvs[])
  >- (cv_termination_tac >> rename1 `cv_fst x` >> Cases_on `x` >> gvs[])
  >- (Cases_on `cv_v` >> gvs[])
QED

Triviality cv_dest_cons_chain_size:
  ∀a x y. cv_dest_cons_chain a = Pair x y ⇒ cv_size y < cv_size a
Proof
  recInduct $ fetch "-" "cv_dest_cons_chain_ind" >> rw[] >>
  pop_assum mp_tac >> simp[Once $ fetch "-" "cv_dest_cons_chain_def"] >>
  rw[AllCaseEqs()] >> gvs[] >> cv_termination_tac
QED

val pre = cv_auto_trans_pre_rec exp2v_def
  (
    WF_REL_TAC ‘measure $ λx. case x of
                               | INL v => cv_size v + 3
                               | INR (INL v) => cv_size v + 3
                               | INR (INR v) => cv_size v’
    \\ cv_termination_tac
    >- (
      irule LESS_EQ_LESS_TRANS >> irule_at Any cv_get_Op_Head_size >>
      irule LESS_EQ_LESS_TRANS >> irule_at Any cv_EL_size >>
      irule LESS_EQ_LESS_TRANS >> goal_assum $ drule_at Any >> simp[]
      )
    >- (
      `k = 3` by gvs[] >> gvs[] >>
      drule cv_dest_case_tree_size >> strip_tac >>
      gvs[cvTheory.cv_eq_def0,
          cv_typeTheory.from_to_bool |> SRULE [cv_typeTheory.from_to_def]] >>
      qpat_x_assum `cv_LENGTH _ = _` mp_tac >>
      simp[Once cv_LENGTH_def] >>
      ntac 2 $ simp[Once cv_LEN_def, AllCaseEqs()] >> strip_tac >>
      cv_termination_tac >> drule cv_dest_case_tree_size >> simp[] >>
      Cases_on `z'` >> gvs[] >>
      qpat_x_assum `cv_dest_case_tree _ _ = _` mp_tac >>
      ntac 2 $ simp[Once cv_EL_def] >>
      simp[Once $ fetch "-" "cv_dest_case_tree_def", AllCaseEqs()] >> rw[] >> gvs[] >>
      rpt $ pop_assum mp_tac >> rpt $ simp[Once $ fetch "-" "cv_dest_case_lets_def"]
      )
    >- (
      `k = 3` by gvs[] >> gvs[] >>
      gvs[cvTheory.cv_eq_def0,
          cv_typeTheory.from_to_bool |> SRULE [cv_typeTheory.from_to_def]] >>
      qpat_x_assum `cv_LENGTH _ = _` mp_tac >> simp[Once cv_LENGTH_def] >>
      ntac 2 $ simp[Once cv_LEN_def, AllCaseEqs()] >> strip_tac >>
      cv_termination_tac >>
      drule cv_dest_case_enum_size >> strip_tac >> gvs[] >>
      Cases_on `z'` >> gvs[] >>
      last_x_assum mp_tac >> simp[Once $ fetch "-" "cv_dest_case_enum_def"] >>
      rw[AllCaseEqs()] >> gvs[] >>
      pop_assum mp_tac >> simp[Once $ fetch "-" "cv_dest_case_enum_def"]
      )
    >- (
      `k = 1` by gvs[] >> gvs[] >>
      drule cv_dest_cons_chain_size >> simp[ADD1] >>
      Cases_on `x2` >> gvs[ADD1] >> Cases_on `z` >> gvs[]
      )
    >- (
      `k = 1` by gvs[] >> gvs[] >>
      drule cv_dest_cons_chain_size >> simp[ADD1] >>
      Cases_on `z` >> gvs[] >>
      last_x_assum mp_tac >> simp[Once $ fetch "-" "cv_dest_cons_chain_def"]
      )
    >- (
      `k = 1` by gvs[] >> gvs[] >>
      drule cv_dest_cons_chain_size >> simp[ADD1] >>
      Cases_on `z` >> gvs[] >>
      last_x_assum mp_tac >> simp[Once $ fetch "-" "cv_dest_cons_chain_def"]
      )
    >- (
      `k = 4` by gvs[] >> gvs[] >>
      Cases_on `z` >> gvs[] >> Cases_on `g'` >> gvs[]
      )
    )

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
