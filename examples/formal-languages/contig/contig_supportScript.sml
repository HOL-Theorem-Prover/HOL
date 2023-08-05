open HolKernel Parse boolLib bossLib BasicProvers pred_setLib stringLib;

open pairTheory arithmeticTheory listTheory rich_listTheory pred_setTheory
     stringTheory combinTheory optionTheory;

val _ = new_theory "contig_support";

Theorem SKOLEM_SUBSET :
  !P Q.
    (!x. P x ==> ?y. Q x y) <=> ?f. !x. P x ==> Q x (f x)
Proof
 metis_tac[]
QED

Theorem IS_SOME_NEG :
 IS_SOME = \x. ~(x=NONE)
Proof
  rw [FUN_EQ_THM] >> metis_tac [NOT_IS_SOME_EQ_NONE]
QED

Theorem strlen_eq :
 !(s:string) m. (STRLEN L = m)
       <=>
       (m = 0 /\ L = []) \/
       (0 < m /\ ?n t. L = CHR n::t /\ n < 256 /\ STRLEN t = m - 1)
Proof
 Induct \\ rw[STRLEN_DEF,EQ_IMP_THM]
 >- (Cases_on ‘L’ >> gvs[STRLEN_DEF] >> metis_tac[CHR_ONTO])
 >- gvs[STRLEN_DEF]
 >- gvs[STRLEN_DEF]

QED

Theorem strlen_eq_1 :
 !L. (STRLEN L = 1) <=> ?n. n < 256 /\ L = [CHR n]
Proof
 rw [Once strlen_eq] \\ metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Some supporting definitions                                               *)
(*---------------------------------------------------------------------------*)

Definition tdrop_def:
  tdrop 0 list acc = SOME (REVERSE acc, list) /\
  tdrop n [] acc = NONE /\
  tdrop (SUC n) (h::t) acc = tdrop n t (h::acc)
End

Theorem tdrop_thm :
 !n list acc acc'.
     tdrop n list acc = SOME (acc',suf)
     <=>
     (acc' ++ suf = REVERSE acc ++ list) /\
     (LENGTH acc' = n + LENGTH acc)
Proof
 recInduct tdrop_ind
 >> rw [tdrop_def,EQ_IMP_THM]
 >- metis_tac [LENGTH_REVERSE]
 >- fs [APPEND_11_LENGTH]
 >- fs [APPEND_11_LENGTH]
 >- (‘LENGTH (acc' ++ suf) = LENGTH acc’ by metis_tac[LENGTH_REVERSE] >>  fs[])
QED

Definition take_drop_def :
  take_drop n list = tdrop n list []
End

Theorem take_drop_thm :
  !n list.
      take_drop n list = SOME (pref,suf) <=> pref ++ suf = list /\ (n = LENGTH pref)
Proof
   rw_tac list_ss [take_drop_def,tdrop_thm] >> metis_tac[]
QED

Definition upto_def:
  upto lo hi = if lo > hi then [] else lo::upto (lo+1) hi
Termination
  WF_REL_TAC ‘measure (\(a,b). b+1n - a)’
End

Theorem upto_interval_thm :
  !lo hi. set(upto lo hi) = {n | lo <= n /\ n <= hi}
Proof
 recInduct upto_ind
  >> rw_tac list_ss []
  >> rw_tac list_ss [Once upto_def]
  >> fs[]
  >> rw [pred_setTheory.EXTENSION]
QED

Theorem length_upto :
  !lo hi. lo <= hi ==> LENGTH(upto lo hi) = (hi-lo) + 1
Proof
 recInduct upto_ind
  >> rw_tac list_ss []
  >> rw_tac list_ss [Once upto_def]
  >> fs[]
  >> ‘lo=hi \/ lo+1 <= hi’ by decide_tac
      >- rw[Once upto_def]
      >- fs[]
QED

(*---------------------------------------------------------------------------*)
(* Definition of a concatenation function                                    *)
(*                                                                           *)
(*    concatPartial : 'a option list -> 'a list option                       *)
(*                                                                           *)
(* The final definition could be made directly, but we proceed by making an  *)
(* iterative version that is more computationally efficient.                 *)
(*---------------------------------------------------------------------------*)

Definition concatPartial_acc_def :
  concatPartial_acc [] acc = SOME acc /\
  concatPartial_acc (NONE::t) acc = NONE /\
  concatPartial_acc (SOME x::t) acc = concatPartial_acc t (x::acc)
End

Definition concatPartial_def :
  concatPartial optlist =
    case concatPartial_acc optlist []
     of NONE => NONE
      | SOME list => SOME (FLAT (REVERSE list))
End

Theorem concatPartial_acc_NONE :
 !optlist acc list.
  (concatPartial_acc optlist acc = NONE)
   <=>
  EXISTS (\x. x=NONE) optlist
Proof
recInduct concatPartial_acc_ind
 >> rw[]
 >> full_simp_tac list_ss [concatPartial_acc_def]
QED

Theorem concatPartial_acc_SOME :
 !optlist acc list.
  (concatPartial_acc optlist acc = SOME list)
   <=>
  EVERY IS_SOME optlist /\
  (list = REVERSE (MAP THE optlist) ++ acc)
Proof
recInduct concatPartial_acc_ind
 >> rw[]
 >> full_simp_tac list_ss [concatPartial_acc_def]
 >> metis_tac []
QED

Theorem concatPartial_NONE :
 !optlist.
  (concatPartial optlist = NONE)
   =
  EXISTS (\x. x=NONE) optlist
Proof
  simp_tac list_ss [concatPartial_def,option_case_eq]
   >> metis_tac[concatPartial_acc_NONE]
QED

Theorem concatPartial_SOME :
 !optlist list.
  (concatPartial optlist = SOME list)
  <=>
  EVERY IS_SOME optlist /\
  (list = FLAT (MAP THE optlist))
Proof
  rw_tac list_ss [concatPartial_def,option_case_eq,concatPartial_acc_SOME]
  >> metis_tac[]
QED

Theorem concatPartial_thm :
 concatPartial optlist =
    if EXISTS (\x. x=NONE) optlist
       then NONE
    else SOME (FLAT (MAP THE optlist))
Proof
 rw[concatPartial_NONE,concatPartial_SOME]
 >> fs [NOT_EXISTS,combinTheory.o_DEF,IS_SOME_NEG]
QED

Theorem concatPartial_nil :
 concatPartial [] = SOME []
Proof
 EVAL_TAC
QED

val _ = export_theory();
