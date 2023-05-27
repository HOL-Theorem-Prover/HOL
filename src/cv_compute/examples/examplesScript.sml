(* -------------------------------------------------------------------------
 * This script contains some instructions on how to use the in-kernel
 * compute primitive, which is exposed by the function cv_computeLib.cv_compute.
 *
 * cv_compute is called with a list of *code equations* and a term to reduce.
 * The term must be of type :cv. A code equation is a theorem of this shape:
 *
 *   |- f (x1:cv) ... (xN:cv) = (e:cv)
 *
 * The term `e` must be closed under the xi:s. All function symbols in `e` must
 * have a corresponding code equation in the list passed to compute. The type
 * :cv is similar to Lisp pairs (but without the nice s-expression syntax). The
 * following constructors can be used to create values of type :cv:
 *
 *   Num  :num -> cv         (* Numbers *)
 *   Pair :cv -> cv -> cv    (* Pairs   *)
 *   cv_add :cv -> cv -> cv  (* arithmetic *)
 *   cv_sub :cv -> cv -> cv
 *   cv_mul :cv -> cv -> cv
 *   cv_div :cv -> cv -> cv
 *   cv_mod :cv -> cv -> cv
 *
 *   cv_lt :cv -> cv -> cv   (* less-than *)
 *   cv_eq :cv -> cv -> cv   (* equality *)
 *
 *   cv_ispair :cv -> cv
 *   cv_fst :cv -> cv
 *   cv_snd :cv -> cv
 *
 * Arithmetic and less-than treats pairs as the number zero. Things of a Boolean
 * nature treat non-zero numbers as true, and everything else as false. Further-
 * more, limited let-bindings and function application are supported:
 *
 *   let (x:cv) = (y:cv) in (z:cv)        where x is a variable
 *   f (x1:cv) ... (xN:cv)                where all xi:s are first-order
 *
 * See cvScript.sml for more details on the various cv_-operations, and the file
 * cv_computeLib.sml for a list of axioms that the different symbols must
 * satisfy.
 * ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib cv_computeLib;
open arithmeticTheory listTheory prim_recTheory cvTheory;

val _ = new_theory "examples";

(* -------------------------------------------------------------------------
 * Example 1: factorial
 *
 * Below is a definition of the factorial function in the :cv type. There is
 * also a proof that factc and FACT compute related values.
 * ------------------------------------------------------------------------- *)

Definition factc_def:
  factc n =
    cv_if (cv_lt n (Num 1))
          (Num 1)
          (cv_mul n (factc (cv_sub n (Num 1))))
Termination
  WF_REL_TAC `measure cv_size_alt`
  \\ Cases \\ simp [cv_size_alt_def, CaseEq "bool"]
End

Theorem factc_is_fact:
  !n. factc (Num n) = Num (FACT n)
Proof
  Induct \\ once_rewrite_tac [factc_def, FACT] \\ simp []
QED

(* cv_compute takes a list of compute equations, and an input term. All function
 * constants in the term must have a code equation. Here, factc_def is the only
 * code equation:
 *)

Triviality factc_test =
  time (cv_compute [factc_def]) ``factc (Num 123)``;

(* Same computation using EVAL:
 *)

Triviality fact_test = time EVAL ``FACT 123``;

(* Using cv_compute as a tactic:
 *)

Triviality fact_12:
  factc (Num 12) = Num 479001600
Proof
  CONV_TAC (TOP_DEPTH_CONV (UNCHANGED_CONV (cv_compute [factc_def])))
  \\ REFL_TAC
QED

(* -------------------------------------------------------------------------
 * Example 2: primality checking using trial division
 *
 * The following functions create a list of primes up to some bound. Primes
 * are found using trial division. Lists are encoded as pairs terminated by
 * the number 0.
 * ------------------------------------------------------------------------- *)

Definition isprimec_aux_def:
  isprimec_aux dvs n =
    cv_if (cv_lt dvs n)
          (cv_if (cv_mod n dvs)
                 (isprimec_aux (cv_add dvs (Num 2)) n)
                 (Num 0))
          (Num 1)
Termination
  WF_REL_TAC `measure (\(dvs,n). cv_size_alt (cv_sub n dvs))`
  \\ Induct \\ simp [PULL_EXISTS]
  \\ Cases_on `dvs` \\ gs [cv_size_alt_def] \\ rw [] \\ gs []
End

Definition isprimec_def:
  isprimec n =
    cv_if (cv_lt n (Num 2))
          (Num 0)
          (cv_if (cv_eq n (Num 2))
                 (Num 1)
                 (cv_if (cv_mod n (Num 2))
                        (isprimec_aux (Num 3) n)
                        (Num 0)))
End

Definition primes_uptoc_def:
  primes_uptoc upto =
    cv_if (cv_ispair upto)
          (Num 0)
          (cv_if (cv_lt (Num 1) upto)
                 (cv_if (isprimec upto)
                        (Pair upto (primes_uptoc (cv_sub upto (Num 1))))
                        (primes_uptoc (cv_sub upto (Num 1))))
                 (Num 0))
Termination
  WF_REL_TAC `measure cv_size_alt`
  \\ conj_tac \\ Cases \\ simp [cv_size_alt_def]
End

(* Here are the corresponding HOL functions, and a proof they compute values
 * that are related to the values computed by the corresponding :cv functions.
 *)

Definition isprime_aux_def:
  isprime_aux dvs n =
    if dvs < n then
      if n SAFEMOD dvs <> 0 then
        isprime_aux (dvs + 2) n
      else F
    else T
Termination
  WF_REL_TAC `measure (\(dvs,n). n - dvs)`
End

Definition isprime_def:
  isprime n =
    if n < 2 then F else
    if n = 2 then T else
    if n MOD 2 = 0 then F
    else isprime_aux 3 n
End

Triviality EVEN_divides:
  EVEN n /\ divides n m ==> EVEN m
Proof
  `divides 2 n /\ divides n m ==> divides 2 m`
    suffices_by (rw [] \\ gs [dividesTheory.compute_divides, EVEN_MOD2])
  \\ simp [dividesTheory.DIVIDES_TRANS, SF SFY_ss]
QED

Triviality isprime_aux_thm:
  !dvs n.
    1 < dvs /\ dvs < n /\
    ~EVEN n /\
    ~EVEN dvs /\
    (!k. 1 < k /\ k < dvs ==> ~divides k n) ==>
       isprime_aux dvs n = prime n
Proof
  ho_match_mp_tac isprime_aux_ind \\ rw []
  \\ rw [Once isprime_aux_def] \\ gs []
  \\ `n MOD dvs <> 0 <=> ~divides dvs n`
    by gvs [dividesTheory.compute_divides]
  \\ pop_assum SUBST_ALL_TAC
  \\ gs [EVEN_ADD]
  \\ Cases_on `divides dvs n` \\ gs []
  >- (
    gs [dividesTheory.prime_def]
    \\ first_x_assum (irule_at Any) \\ gs [])
  \\ `~divides (dvs + 1) n`
    by (strip_tac
        \\ `EVEN (dvs + 1)`
          by gs [GSYM ADD1, EVEN]
        \\ drule_then assume_tac EVEN_divides
        \\ gs [])
  \\ Cases_on `n <= dvs + 2` \\ gs []
  >- (
    simp [Once isprime_aux_def]
    \\ gvs [LESS_OR_EQ, NOT_LESS]
    >- (
      `n = dvs + 1` by decide_tac
      \\ gvs [EVEN, GSYM ADD1])
    \\ rw [dividesTheory.prime_def, DISJ_EQ_IMP]
    \\ CCONTR_TAC \\ gs []
    \\ first_x_assum (qspec_then `b` assume_tac)
    \\ gvs [dividesTheory.compute_divides, NOT_LESS, LESS_OR_EQ]
    \\ `(dvs + 2) MOD b = dvs + 2`
      suffices_by (strip_tac \\ gs [])
    \\ simp []
    \\ CCONTR_TAC \\ gvs [NOT_LESS, LESS_OR_EQ]
    \\ `b = dvs + 1` by decide_tac \\ gvs []
    \\ `(SUC (dvs + 1)) MOD (dvs + 1) = 1`
      by gs []
    \\ rgs [ADD1])
  \\ first_x_assum (irule_at Any)
  \\ rw [] \\ gs []
  \\ `k < dvs \/ k = dvs \/ k = dvs + 1` by decide_tac \\ gvs []
QED

Theorem isprime_is_prime:
  !n. isprime n <=> prime n
Proof
  rw [isprime_def]
  \\ Cases_on `n <= 2` \\ gs [DECIDE ``!n. n <= 2 <=> n = 0 \/ n = 1 \/ n = 2``]
  \\ Cases_on `n MOD 2 = 0` \\ gs []
  >- (
    csimp [dividesTheory.prime_def, dividesTheory.compute_divides]
    \\ first_x_assum (irule_at Any) \\ gs [])
  \\ Cases_on `n = 3` \\ gs []
  >- simp [Once isprime_aux_def]
  \\ irule isprime_aux_thm
  \\ dsimp [EVEN_MOD2]
  \\ CCONTR_TAC \\ gs [DECIDE ``!k. k < 3 <=> k = 0 \/ k = 1 \/ k = 2``,
                       dividesTheory.compute_divides, NOT_LESS, LESS_OR_EQ]
QED

Definition primes_upto_def:
  primes_upto upto =
    if 1 < upto then
      if isprime upto then
        upto :: primes_upto (upto - 1)
      else
        primes_upto (upto - 1)
    else
      []
End

Triviality isprimec_aux_isprime_aux:
  !m n. isprimec_aux (Num m) (Num n) = b2c (isprime_aux m n)
Proof
  ho_match_mp_tac isprime_aux_ind \\ rw []
  \\ once_rewrite_tac [isprimec_aux_def, isprime_aux_def] \\ simp []
  \\ rw [] \\ gvs [CaseEq "bool"]
  \\ Cases_on `n SAFEMOD m` \\ gs []
QED

Triviality isprimec_is_isprime:
  !n. isprimec (Num n) = b2c (isprime n)
Proof
  rw [isprimec_def, isprime_def]
  \\ rw [DISJ_EQ_IMP] \\ gs [isprimec_aux_isprime_aux, CaseEq "bool"]
  \\ Cases_on `n = 2` \\ gs []
  \\ Cases_on `n MOD 2` \\ gvs []
QED

Theorem primes_uptoc_is_primes_upto:
  !n. primes_uptoc (Num n) = ns2c (primes_upto n)
Proof
  ho_match_mp_tac primes_upto_ind \\ rw []
  \\ once_rewrite_tac [primes_uptoc_def, primes_upto_def]
  \\ simp [CaseEq "bool", isprimec_is_isprime]
  \\ rw [] \\ gvs [ns2c_def]
QED

(* To compute with `primes_uptoc`, all function definitions must be passed to
 * cv_compute as code equations:
 *)

Triviality primes_test1 =
  time (cv_compute [primes_uptoc_def, isprimec_def, isprimec_aux_def])
       ``primes_uptoc (Num 123)``;

Triviality primes_test2 = time EVAL ``primes_upto 123``;

val _ = export_theory ();

