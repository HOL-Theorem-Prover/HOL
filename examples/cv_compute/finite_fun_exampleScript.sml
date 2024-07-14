open HolKernel Parse boolLib bossLib;
open wordsTheory wordsLib cv_stdTheory cv_transLib;
open cv_typeTheory sptreeTheory;

val _ = new_theory "finite_fun_example";

(* --- setup --- *)

Type mem = “:256 word -> num”;

Definition to_mem_def:
  to_mem cv =
    let t = to_sptree_spt cv$c2n cv in
      FOLDR (λ(a,v) f. (n2w a =+ v) f) (λa. 0) (toSortedAList t) :mem
End

Definition build_spt_def:
  build_spt 0 (m:mem) = LN ∧
  build_spt (SUC a) m =
    if m (n2w a) = 0 then build_spt a m else
      insert a (m (n2w a)) (build_spt a m)
End

Definition from_mem_def:
  from_mem (m:mem) =
    from_sptree_sptree_spt Num (build_spt (dimword (:256)) m)
End

Triviality wf_build_spt[simp]:
  ∀n m. wf (build_spt n m)
Proof
  Induct \\ gvs [build_spt_def] \\ rw [] \\ gvs [wf_insert]
QED

Triviality lookup_build_spt_lemma1:
  ∀k n. n < k ⇒ lookup n (build_spt k x) = lookup n (build_spt (SUC n) x)
Proof
  Induct \\ gvs []
  \\ strip_tac
  \\ Cases_on ‘n = k’ \\ gvs []
  \\ simp [Once build_spt_def]
  \\ rw [] \\ gvs [lookup_insert]
QED

Triviality lookup_build_spt_lemma2:
  ∀k n. k ≤ n ⇒ lookup n (build_spt k x) = NONE
Proof
  Induct \\ gvs [build_spt_def] \\ rw [lookup_insert]
QED

Triviality to_mem_eq:
  (∀n. n ∈ domain t ⇒ n < dimword (:'a)) ⇒
  FOLDR (λ(a,v) f. f⦇n2w a ↦ v⦈) (λ(a:'a word). 0) (toSortedAList t) =
    (λa. case lookup (w2n a) t of
         | NONE => 0n
         | SOME n => n)
Proof
  gvs [to_mem_def,FUN_EQ_THM,domain_lookup,PULL_EXISTS]
  \\ rewrite_tac [GSYM MEM_toSortedAList]
  \\ rewrite_tac [GSYM ALOOKUP_toSortedAList]
  \\ qspec_tac (‘toSortedAList t’,‘xs’)
  \\ Induct \\ gvs [pairTheory.FORALL_PROD,combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac
  \\ Cases_on ‘a’ \\ gvs []
  \\ rw [] \\ gvs []
  \\ gvs [SF DNF_ss, SF SFY_ss]
QED

Theorem from_to_mem[cv_from_to]:
  from_to from_mem to_mem
Proof
  gvs [from_to_def,to_mem_def,from_mem_def,FUN_EQ_THM,
       cv_typeLib.from_to_thm_for “:num spt” |> SRULE [cv_typeTheory.from_to_def]]
  \\ gen_tac
  \\ dep_rewrite.DEP_REWRITE_TAC [to_mem_eq] \\ gvs []
  \\ conj_tac
  >- (gvs [domain_lookup] \\ rpt strip_tac
      \\ CCONTR_TAC \\ gvs [lookup_build_spt_lemma2])
  \\ Cases \\ rw [] \\ gvs []
  \\ simp [lookup_build_spt_lemma1] \\ rw [build_spt_def]
  \\ simp [lookup_build_spt_lemma2]
QED

Definition mem_lookup_def:
  mem_lookup a (m:mem) = m a
End

Definition mem_update_def:
  mem_update a v (m:mem) = (a =+ v) m
End

Definition mem_empty_def:
  mem_empty = ((λa. 0):mem)
End

Definition cv_mem_lookup_def:
  cv_mem_lookup (a:cv) (m:cv) =
    let res = cv_lookup a m in
      cv_if (cv_ispair res) (cv_snd res) (Num 0)
End

Definition cv_mem_update_def:
  cv_mem_update (a:cv) (v:cv) (m:cv) =
    cv_if (cv_eq v (Num 0))
      (cv_delete a m)
      (cv_insert a v m)
End

Theorem mem_empty_cv_rep[cv_rep]:
  from_mem mem_empty = Num 0
Proof
  gvs [from_mem_def]
  \\ qsuff_tac ‘∀n. build_spt n mem_empty = LN’
  >- (gvs [] \\ EVAL_TAC)
  \\ Induct \\ gvs [build_spt_def,mem_empty_def]
QED

Theorem mem_lookup_cv_rep[cv_rep]:
  Num (mem_lookup a m) =
  cv_mem_lookup (from_word a) (from_mem m)
Proof
  gvs [mem_lookup_def,cv_mem_lookup_def,from_mem_def,from_word_def]
  \\ gvs [GSYM cv_lookup_thm]
  \\ rewrite_tac [GSYM (EVAL “dimword (:256)”)]
  \\ Cases_on ‘lookup (w2n a) (build_spt (dimword (:256)) m)’ \\ gvs []
  \\ gvs [from_option_def]
  \\ pop_assum mp_tac
  \\ qspec_then ‘a’ assume_tac w2n_lt
  \\ dxrule lookup_build_spt_lemma1 \\ gvs []
  \\ gvs [build_spt_def] \\ rw [] \\ gvs [lookup_insert] \\ rw []
  \\ gvs [lookup_build_spt_lemma2]
QED

Theorem mem_update_cv_rep[cv_rep]:
  from_mem (mem_update a v m) =
  cv_mem_update (from_word a) (Num v) (from_mem m)
Proof
  gvs [mem_update_def,cv_mem_update_def,from_mem_def,from_word_def]
  \\ Cases_on ‘v = 0’ \\ gvs [GSYM cv_delete_thm]
  \\ gvs [GSYM cv_insert_thm] \\ AP_TERM_TAC
  \\ dep_rewrite.DEP_REWRITE_TAC [sptreeTheory.spt_eq_thm]
  \\ gvs [lookup_delete,wf_delete,wf_insert,lookup_insert]
  \\ rw [] \\ gvs []
  \\ qspec_then ‘a’ assume_tac w2n_lt
  \\ dxrule lookup_build_spt_lemma1 \\ gvs [] \\ rw []
  \\ gvs [build_spt_def] \\ rw [] \\ gvs [lookup_insert] \\ rw []
  \\ gvs [lookup_build_spt_lemma2]
  \\ Cases_on ‘n < dimword (:256)’
  \\ gvs [lookup_build_spt_lemma1,lookup_build_spt_lemma2]
  \\ Cases_on ‘a’ \\ gvs []
  \\ gvs [build_spt_def,combinTheory.APPLY_UPDATE_THM]
  \\ rw [] \\ gvs [lookup_build_spt_lemma2]
QED

Theorem to_mem_funs =
  LIST_CONJ [mem_empty_def,mem_lookup_def,mem_update_def] |> GSYM;

(* --- test --- *)

Definition mem_test_def:
  mem_test (mem1:mem) (mem2:mem) a =
   if mem1 a + mem2 a < 100 then
     mem2⦇60w ↦ 45; a ↦ mem1 a + 1⦈
   else (λa. 0)
End

val _ = cv_trans (mem_test_def |> SRULE [to_mem_funs]);

val th = fetch "-" "cv_mem_test_thm";
val def = fetch "-" "cv_mem_test_def";

val res = cv_eval “mem_test mem_empty mem_empty 3w”;

val _ = export_theory();
