(* Support theorems and definitions for the in-kernel compute primitive:
 * cv_computeLib.cv_compute.
 *
 * The kernel compute primitive accepts closed terms written using terms in the
 * :cv type, using the functions below (e.g., cv_add, cv_if, ...). See the
 * files in examples/ for examples showcasing usage of the primitive.
 *
 *)

open HolKernel boolLib bossLib arithmeticTheory prim_recTheory;

val _ = new_theory "cv";

(* -------------------------------------------------------------------------
 * Definition of the cv type and its operations.
 * ------------------------------------------------------------------------- *)

Datatype:
  cv = Pair cv cv
     | Num num
End

Definition cv_add_def[simp]:
  cv_add (Num m) (Num n) = Num (m + n) /\
  cv_add (Num m) (Pair p q) = Num m /\
  cv_add (Pair p q) (Num n) = Num n /\
  cv_add (Pair p q) (Pair r s) = Num 0
End

Definition cv_sub_def[simp]:
  cv_sub (Num m) (Num n) = Num (m - n) /\
  cv_sub (Num m) (Pair p q) = Num m /\
  cv_sub (Pair p q) (Num n) = Num 0 /\
  cv_sub (Pair p q) (Pair r s) = Num 0
End

Definition cv_mul_def[simp]:
  cv_mul (Num m) (Num n) = Num (m * n) /\
  cv_mul (Num m) (Pair p q) = Num 0 /\
  cv_mul (Pair p q) (Num n) = Num 0 /\
  cv_mul (Pair p q) (Pair r s) = Num 0
End

Definition SAFEDIV_def:
  SAFEDIV m n = if n = 0 then 0 else m DIV n
End

val _ = Parse.add_infix ("SAFEDIV", 600, HOLgrammars.LEFT);

Definition cv_div_def[simp]:
  cv_div (Num m) (Num n) = Num (m SAFEDIV n) /\
  cv_div (Num m) (Pair p q) = Num 0 /\
  cv_div (Pair p q) (Num n) = Num 0 /\
  cv_div (Pair p q) (Pair r s) = Num 0
End

Definition SAFEMOD_def:
  SAFEMOD m n = if n = 0 then m else m MOD n
End

val _ = Parse.add_infix ("SAFEMOD", 650, HOLgrammars.LEFT);

Definition cv_mod_def[simp]:
  cv_mod (Num m) (Num n) = Num (m SAFEMOD n) /\
  cv_mod (Num m) (Pair p q) = Num m /\
  cv_mod (Pair p q) (Num n) = Num 0 /\
  cv_mod (Pair p q) (Pair r s) = Num 0
End

Definition cv_lt_def[simp]:
  cv_lt (Num m) (Num n) = Num (if m < n then SUC 0 else 0) /\
  cv_lt (Num m) (Pair p q) = Num 0 /\
  cv_lt (Pair p q) (Num n) = Num 0 /\
  cv_lt (Pair p q) (Pair r s) = Num 0
End

Definition cv_eq_def:
  cv_eq (p:cv) (q:cv) = Num (if p = q then SUC 0 else 0)
End

Definition cv_fst_def[simp]:
  cv_fst (Pair p q) = p /\
  cv_fst (Num m) = Num 0
End

Definition cv_snd_def[simp]:
  cv_snd (Pair p q) = q /\
  cv_snd (Num m) = Num 0
End

Definition cv_ispair_def[simp]:
  cv_ispair (Pair p q) = Num (SUC 0) /\
  cv_ispair (Num m) = Num 0
End

Definition cv_if_def:
  cv_if (Num (SUC m)) (p:cv) (q:cv) = p /\
  cv_if (Num 0) p q = q /\
  cv_if (Pair r s) p q = q
End

(* -------------------------------------------------------------------------
 * Misc. simplifications, etc.
 * ------------------------------------------------------------------------- *)

Definition c2b_def[simp]:
  c2b x = (?k. x = Num (SUC k))
End

Definition b2c_def[simp]:
  (b2c T = Num (SUC 0)) /\
  (b2c F = Num 0)
End

Theorem b2c[simp]:
  ((b2c x = Num 1) = x) /\
  (b2c x = Num (SUC 0)) = x
Proof
  Cases_on `x` \\ rw []
QED

Definition c2ns_def:
  c2ns x =
    case x of
      Num 0 => []
    | Pair (Num n) y => n :: c2ns y
End

Definition ns2c_def:
  (ns2c [] = Num 0) /\
  (ns2c (y::ys) = Pair (Num y) (ns2c ys))
End

Theorem SAFEDIV[simp]:
  (m SAFEDIV 0 = 0) /\
  (n <> 0 ==> m SAFEDIV n = m DIV n)
Proof
  rw [SAFEDIV_def]
QED

Theorem SAFEMOD[simp]:
  (m SAFEMOD 0 = m) /\
  (n <> 0 ==> m SAFEMOD n = m MOD n)
Proof
  rw [SAFEMOD_def]
QED

Theorem cv_eq[simp]:
  (cv_eq (Pair x y) (Pair x' y') = b2c (x = x' /\ y = y')) /\
  (cv_eq (Num m) (Num n) = b2c (m = n)) /\
  (cv_eq (Pair x y) (Num n) = b2c F) /\
  (cv_eq (Num n) (Pair x y) = b2c F)
Proof
  rw [cv_eq_def]
QED

Theorem cv_if_cong[defncong]:
  (c2b P = c2b Q) /\
  (c2b Q ==> x = x') /\
  (~c2b Q ==> y = y') ==>
    cv_if P x y = cv_if Q x' y'
Proof
  Cases_on `P` \\ Cases_on `Q` \\ gs [c2b_def, cv_if_def]
  \\ Cases_on `n` \\ gs [c2b_def, cv_if_def]
  \\ Cases_on `n'` \\ gs [c2b_def, cv_if_def]
QED

Theorem cv_if[simp]:
  cv_if x y z = if c2b x then y else z
Proof
  rw [] \\ simp [cv_if_def]
  \\ rename [`cv_if x`] \\ namedCases_on `x` ["","n"] \\ simp [cv_if_def]
  \\ Cases_on `n` \\ gs [cv_if_def]
QED

Theorem cv_extras[simp]:
  (cv_lt v (Pair x y) = Num 0) /\
  (cv_lt (Pair x y) v = Num 0) /\
  (cv_add (Pair x y) v = case v of Pair a b => Num 0 | _ => v) /\
  (cv_add v (Pair x y) = case v of Pair a b => Num 0 | _ => v) /\
  (cv_sub (Pair x y) v = Num 0) /\
  (cv_sub v (Pair x y) = case v of Pair a b => Num 0 | _ => v) /\
  (cv_mul (Pair x y) v = Num 0) /\
  (cv_mul v (Pair x y) = Num 0) /\
  (cv_div (Pair x y) v = Num 0) /\
  (cv_div v (Pair x y) = case v of Pair a b => Num 0 | _ => Num 0) /\
  (cv_mod (Pair x y) v = Num 0) /\
  (cv_mod v (Pair x y) = case v of Pair a b => Num 0 | _ => v)
Proof
  Cases_on `v` \\ simp [cv_lt_def, cv_add_def, cv_sub_def, cv_mul_def,
                        cv_div_def, cv_mod_def, CaseEq "bool"]
QED

Definition cv_size_alt_def:
  (cv_size_alt (Num n) = n) /\
  (cv_size_alt (Pair p q) = 1 + cv_size_alt p + cv_size_alt q)
End

(* -------------------------------------------------------------------------
 * Extra characteristic theorems
 * ------------------------------------------------------------------------- *)

Theorem SAFEDIV_RECURSIVE:
  m SAFEDIV n =
    if n = 0 then 0 else
    if m < n then 0 else
    SUC ((m - n) SAFEDIV n)
Proof
  rw [] \\ gs [SAFEDIV_def, NOT_ZERO_LT_ZERO, LESS_DIV_EQ_ZERO, LESS_THM,
               NOT_LESS, LESS_OR_EQ]
  \\ irule DIV_UNIQUE
  \\ qexists_tac `(m - n) MOD n`
  \\ simp [ADD1, LEFT_ADD_DISTRIB,
           DECIDE ``n:num <= m ==> (m = n + k <=> m - n = k)``]
  \\ once_rewrite_tac [MULT_COMM] \\ simp [DIVISION]
QED

Theorem SAFEMOD_RECURSIVE:
  m SAFEMOD n =
    if n = 0 then m else
    if m < n then m else
    (m - n) SAFEMOD n
Proof
  rw [] \\ gs [SAFEMOD_def, NOT_ZERO_LT_ZERO, LESS_MOD, LESS_THM, NOT_LESS,
               LESS_OR_EQ, SUB_MOD]
QED

Theorem LT_RECURSIVE:
  ((m < 0) = F) /\
  ((m < SUC n) = (if m = n then T else m < n))
Proof
  DECIDE_TAC
QED

Theorem SUC_EQ:
  ((SUC m = 0) = F) /\
  ((SUC m = SUC n) = (m = n))
Proof
  DECIDE_TAC
QED

Theorem CV_EQ:
  ((Pair p q = Pair r s) = (if p = r then q = s else F)) /\
  ((Pair p q = Num n) = F) /\
  ((Num m = Num n) = (m = n))
Proof
  simp []
QED

val _ = export_theory ();

