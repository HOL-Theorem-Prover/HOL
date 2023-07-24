(* An example using the in-kernel compute rule for reducing terms with numerals.
 *
 * The conversion can reduce arithmetic terms containing the operations
 * +/-/*/DIV/MOD/EXP on numerals.
 *
 * This file contains support theorems and a :cv definition of exponentiation.
 * See knumsLib for the implementation of the conversion.
 *)

open HolKernel boolLib bossLib;
open arithmeticTheory cvTheory;

val _ = new_theory "cv_nums";

val _ = augment_srw_ss [rewrites [c2b_def]]

Definition n2c_def:
  n2c n = Num n
End

Definition c2n_def:
  c2n (Num n) = n
End

Theorem c2n_n2c:
  !x. c2n (n2c x) = x
Proof
  rw [n2c_def, c2n_def]
QED

Theorem n2c_add:
  n2c m = x ==>
  n2c n = y ==>
      n2c (m + n) = cv_add x y
Proof
  rw [n2c_def] \\ rw [cv_add_def]
QED

Theorem n2c_sub:
  n2c m = x ==>
  n2c n = y ==>
      n2c (m - n) = cv_sub x y
Proof
  rw [n2c_def] \\ rw [cv_sub_def]
QED

Theorem n2c_mul:
  n2c m = x ==>
  n2c n = y ==>
      n2c (m * n) = cv_mul x y
Proof
  rw [n2c_def] \\ rw [cv_mul_def]
QED

Theorem n2c_div:
  n2c m = x ==>
  n2c n = y ==>
      n2c (m DIV n) = cv_div x y
Proof
  rw [n2c_def] \\ rw [cv_div_def]
QED

Theorem n2c_mod:
  n2c m = x ==>
  n2c n = y ==>
      n2c (m MOD n) = cv_mod x y
Proof
  rw [n2c_def] \\ rw [cv_mod_def]
QED

Definition EXP2_def:
  EXP2 b e =
    if 0 < e then
      if EVEN e then
        EXP2 b (e DIV 2) * EXP2 b (e DIV 2)
      else
        b * EXP2 b (e - 1)
    else 1
End

Theorem EXP2_EXP:
  !b e. EXP2 b e = b ** e
Proof
  ho_match_mp_tac EXP2_ind \\ rw []
  \\ simp [Once EXP2_def]
  \\ IF_CASES_TAC \\ gs []
  \\ IF_CASES_TAC \\ gs []
  \\ Cases_on `b = 0 \/ b = 1`
  \\ gvs [ZERO_EXP, EVEN_MOD2, DIV_EQ_0]
  \\ rw [] \\ gs [GSYM EXP_EXP_MULT]
  >- (
    `0 < 2` by gs []
    \\ drule_then (qspec_then `e` mp_tac) DIVISION \\ gs [])
  \\ qspecl_then [`e`,`1`,`b`] mp_tac EXP_SUB \\ rw []
  \\ `0 < b` by gs []
  \\ drule_then (qspec_then `b ** e` mp_tac) DIVISION
  \\ rw [] \\ gs [ZERO_EXP]
QED

Definition cv_exp_def:
  cv_exp b e =
    cv_if e                                        (* e is a positive number *)
          (cv_if (cv_mod e (Num 2))                (* e is odd               *)
                 (cv_mul b (cv_exp b (cv_sub e (Num 1))))
                 (let x = cv_exp b (cv_div e (Num 2))
                  in cv_mul x x))
          (Num 1)
Termination
  WF_REL_TAC `measure (cv_size o SND)`
  \\ conj_tac \\ Cases \\ simp [cv_size_def]
End

Theorem n2c_exp:
  n2c m = x ==>
  n2c n = y ==>
      n2c (m EXP n) = cv_exp x y
Proof
  rw [n2c_def]
  \\ `!x y. !m n. x = Num m /\ y = Num n ==> cv_exp x y = Num (EXP2 m n)`
    suffices_by rw [EXP2_EXP]
  \\ ho_match_mp_tac cv_exp_ind \\ rw []
  \\ once_rewrite_tac [cv_exp_def, EXP2_def] \\ simp [EVEN_MOD2]
  \\ Cases_on `n = 0` \\ gs []
  \\ `?k. n = SUC k`
    by (Cases_on `n` \\ gs [])
  \\ gs []
  \\ IF_CASES_TAC \\ gs []
  \\ IF_CASES_TAC \\ gs []
  \\ Cases_on `SUC k MOD 2` \\ gs []
QED

val _ = export_theory ();
