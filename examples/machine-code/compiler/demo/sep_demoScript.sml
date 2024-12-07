
open HolKernel boolLib bossLib Parse;

open codegen_x86Lib;

open compilerLib codegen_x86Lib helperLib;
open set_sepTheory;
open arithmeticTheory;
open wordsTheory

val _ = new_theory "sep_demo";

val (th1,copy_loop_def,th3) = compile "arm" ``
  copy_loop (r0:word32,r1:word32,r2:word32,dg:word32 set,g:word32->word32) =
    if r0 = 0w then (r0,r1,r2,dg,g) else
      let r0 = r0 - 1w in
      let r3 = g r1 in
      let g = (r2 =+ r3) g in
      let r1 = r1 + 4w in
      let r2 = r2 + 4w in
        copy_loop (r0,r1,r2,dg,g)``;

Definition array_def:
  array a [] = emp ∧
  array a (x::xs) = one (a,x) * array (a + 4w:word32) xs
End

(*
 SCONV [array_def,STAR_ASSOC,SEP_CLAUSES] “array a [x1;x2;x3]”
*)

Triviality LESS_EQ_LENGTH_IMP:
  ∀xs m. m <= LENGTH xs ⇒ ∃ys zs. xs = ys ++ zs ∧ LENGTH ys = m
Proof
  Induct \\ gvs [] \\ Cases_on ‘m’ \\ gvs []
  \\ rw [] \\ first_x_assum drule \\ strip_tac
  \\ gvs [listTheory.LENGTH_CONS,PULL_EXISTS]
  \\ irule_at Any EQ_REFL \\ fs []
QED

Theorem array_append:
  ∀xs ys a.
    array a (xs ++ ys) = array a xs * array (a + 4w * n2w (LENGTH xs)) ys
Proof
  Induct \\ gvs [array_def,SEP_CLAUSES,ADD1,word_mul_n2w]
  \\ gvs [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
  \\ gvs [AC STAR_COMM STAR_ASSOC]
QED

Theorem array_LENGTH:
  (array a xs * frame) (fun2set (g,dg)) ⇒
  LENGTH xs ≤ 2**30
Proof
  rw [] \\ CCONTR_TAC \\ gvs [GSYM NOT_LESS]
  \\ ‘1073741824 <= LENGTH xs’ by fs []
  \\ imp_res_tac LESS_EQ_LENGTH_IMP
  \\ gvs []
  \\ Cases_on ‘ys’ \\ Cases_on ‘zs’ \\ gvs []
  \\ gvs [ADD1]
  \\ gvs [array_def,array_append]
  \\ ‘a ≠ a + 0x4w * n2w (LENGTH t) + 0x4w’ by SEP_NEQ_TAC
  \\ pop_assum mp_tac \\ gvs []
  \\ gvs [addressTheory.word_arith_lemma1,word_mul_n2w]
  \\ ‘LENGTH t = 2**30-1’ by gvs [] \\ gvs []
  \\ once_rewrite_tac [GSYM n2w_mod] \\ simp []
QED

Theorem copy_loop_thm:
  ∀xs ys frame r1 r2 dg g r0' r1' r2' dg' g'.
    copy_loop (n2w (LENGTH xs),r1,r2,dg,g) = (r0',r1',r2',dg',g') ∧
    (array r1 xs * array r2 ys * frame) (fun2set (g,dg)) ∧
    LENGTH xs = LENGTH ys (* ∧ LENGTH xs < 2 ** 32 *)
    ⇒
    (array r1 xs * array r2 xs * frame) (fun2set (g',dg'))
Proof
  Induct
  >- (simp [Once copy_loop_def])
  \\ simp [Once copy_loop_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC
  >-
   (rpt strip_tac
    \\ fs [GSYM STAR_ASSOC]
    \\ drule array_LENGTH
    \\ strip_tac \\ gvs [])
  \\ simp [ADD1]
  \\ rewrite_tac [GSYM word_add_n2w]
  \\ simp []
  \\ Cases_on ‘ys’ \\ gvs [ADD1]
  \\ simp [array_def]
  \\ rpt strip_tac
  (* manual way of doing it:
  \\ ‘g r1 = h’ by SEP_READ_TAC
  \\ pop_assum (fn th => fs [th])
  *)
  \\ SEP_R_TAC
  \\ qpat_x_assum ‘copy_loop _ = _’ mp_tac
  \\ SEP_W_TAC
  \\ strip_tac
  \\ last_x_assum drule
  \\ rename [‘LENGTH xs = LENGTH ys’]
  \\ disch_then $ qspec_then ‘ys’ mp_tac
  \\ simp []
  \\ strip_tac
  \\ SEP_F_TAC
  \\ simp [AC STAR_ASSOC STAR_COMM]
QED

val _ = export_theory();
