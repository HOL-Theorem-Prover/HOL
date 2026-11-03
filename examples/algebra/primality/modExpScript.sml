(* -------------------------------------------------------------------------
   Kernel computation equations for modular exponentiation

   Documentation
   Supply a binary modular-power program in the kernel CV language.
   The identities need no primality assumption, including at modulus zero.

   Public interface
   - modExp_cv_modpow_def specifies the CV result;
     modExp_cv_modpow_eq is its executable binary recursion equation.
   - modExp_modpow_to_cv connects natural a ** e MOD n to that program.

   modExpLib uses these proved equations for conversions;
   evaluating candidate arithmetic is not an additional oracle.
   ------------------------------------------------------------------------- *)

Theory modExp
Ancestors
  arithmetic cv

(* These identities are independent of primality, including at modulus zero. *)
Theorem modExp_pow_even[local]:
  !a k n. a ** (2 * k) MOD n =
    ((a ** k MOD n) * (a ** k MOD n)) MOD n
Proof
  simp_tac bool_ss [EXP_ADD, TIMES2, MOD_TIMES2]
QED

Theorem modExp_pow_odd[local]:
  !a k n. a ** (2 * k + 1) MOD n =
    ((a MOD n) * (((a ** k MOD n) * (a ** k MOD n)) MOD n)) MOD n
Proof
  rpt gen_tac >>
  `2 * k + 1 = SUC (2 * k)` by decide_tac >>
  PURE_ONCE_REWRITE_TAC [ASSUME ``2 * k + 1 = SUC (2 * k)``] >>
  PURE_REWRITE_TAC [EXP] >>
  PURE_ONCE_REWRITE_TAC [GSYM modExp_pow_even] >>
  PURE_REWRITE_TAC [MOD_TIMES2] >> REFL_TAC
QED

Theorem modExp_pow_split[local]:
  !a e n. a ** e MOD n =
    if e = 0 then 1 MOD n else
      let r = a ** (e DIV 2) MOD n in
      let s = (r * r) MOD n in
        if e MOD 2 = 0 then s else ((a MOD n) * s) MOD n
Proof
  rpt gen_tac >> Cases_on `e = 0` >- simp[] >>
  qabbrev_tac `k = e DIV 2` >>
  `e = k * 2 + e MOD 2 /\ e MOD 2 < 2` by
    (qunabbrev_tac `k` >>
     metis_tac [DIVISION, DECIDE ``(0:num) < 2``]) >>
  asm_simp_tac bool_ss [LET_THM] >>
  IF_CASES_TAC
  >- (`e = 2 * k` by metis_tac [MULT_COMM, ADD_CLAUSES] >>
      metis_tac [modExp_pow_even]) >>
  `e MOD 2 = 1` by decide_tac >>
  `e = 2 * k + 1` by metis_tac [MULT_COMM] >>
  metis_tac [modExp_pow_odd]
QED

(* A semantic definition avoids adding a recursive definition or a termination
   obligation to the trusted evaluator.  Only the proved code equation below
   is executed; this EXP is never unfolded by the computation library. *)
Definition modExp_cv_modpow_def:
  modExp_cv_modpow a e n =
    cv$Num ((cv$c2n a ** cv$c2n e) MOD cv$c2n n)
End

Theorem modExp_cv_nat_ops[local]:
  (!a b. cv_mul a b = cv$Num (cv$c2n a * cv$c2n b)) /\
  (!a b. cv_div a b = cv$Num (cv$c2n a DIV cv$c2n b)) /\
  (!a b. cv_mod a b = cv$Num (cv$c2n a MOD cv$c2n b))
Proof
  rpt conj_tac >> rpt gen_tac >> Cases_on `a` >> Cases_on `b` >>
  simp [cv_mul_def, cv_div_def, cv_mod_def, c2n_def]
QED

Theorem modExp_cv_if_nat[local]:
  !e p q. cv_if e p q = if cv$c2n e = 0 then q else p
Proof
  rpt gen_tac >> Cases_on `e` >-
    (Cases_on `m` >> simp [cv_if_def, c2n_def]) >>
  simp [cv_if_def, c2n_def]
QED

(* One recursive call, shared by Let, and one square per exponent bit.  All
   arguments are distinct CV variables, as required by kernel code equations. *)
Theorem modExp_cv_modpow_eq:
  modExp_cv_modpow a e n =
    cv_if e
      (let r = modExp_cv_modpow a (cv_div e (cv$Num 2)) n in
       let s = cv_mod (cv_mul r r) n in
         cv_if (cv_mod e (cv$Num 2))
           (cv_mod (cv_mul (cv_mod a n) s) n) s)
      (cv_mod (cv$Num 1) n)
Proof
  CONV_TAC (LAND_CONV (REWR_CONV modExp_cv_modpow_def)) >>
  CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV modExp_pow_split))) >>
  simp_tac bool_ss [modExp_cv_modpow_def, modExp_cv_nat_ops,
                    modExp_cv_if_nat, c2n_def, LET_THM] >>
  rpt IF_CASES_TAC >> fs[]
QED

Theorem modExp_modpow_to_cv:
  !a e n. a ** e MOD n =
    cv$c2n (modExp_cv_modpow (cv$Num a) (cv$Num e) (cv$Num n))
Proof
  simp [modExp_cv_modpow_def, c2n_def]
QED
