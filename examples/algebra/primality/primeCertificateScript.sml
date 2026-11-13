Theory primeCertificate
Ancestors
arithmetic divides gcd list rich_list number prime ring pred_set combinatorics



Theorem prime_divides_product[local]:
(* euclidean property of primes *)
prime q ⇒
(q divides (a * b ) ⇔ q divides a ∨ q divides b)
Proof
metis_tac[P_EUCLIDES, DIVIDES_MULT,MULT_COMM]
QED


Theorem phi_eq_imp_prime[local]:
∀n. 1 < n ∧ phi n = n - 1 ⇒ prime n
Proof
rpt strip_tac >>
 `0 ≤ n` by  fs [] >>
 `CARD (Euler n) =  CARD (residue n)`
 by  gvs [totient_def, phi_eq_totient, residue_card] >>
 `Euler n  = residue n` by rw [ Euler_thm,residue_finite,Euler_finite,SUBSET_EQ_CARD]
  >> rewrite_tac [prime_def] >>  gvs [] >> rpt strip_tac >>
  rename1 `d divides n` >>
  `d ≤ n` by (imp_res_tac DIVIDES_LEQ_OR_ZERO >> decide_tac)
  >> Cases_on `d = n` >> simp [] >>
 `0 < d ` by  metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO ] >>
 `d ∈ residue n` by  fs [ residue_def]  >>
 `coprime n d ` by metis_tac [Euler_element]  >>
  metis_tac [coprime_common_factor, DIVIDES_REFL]
QED


Theorem divisor_prime_extension[local]:
∀ d k. 0 < d ∧ d divides k ∧ d < k
    ⇒
(∃ q. prime q ∧ q divides k ∧ d divides ( k DIV q))
Proof
rpt strip_tac >>
  `k = d * (k DIV d)` by (gvs [DIVIDES_EQN_COMM]  ) >>
  `k DIV d ≠ 1` by ( strip_tac >> fs[]) >>
  `?q. prime q /\ q divides (k DIV d)` by
    gvs [PRIME_FACTOR] >>
  `0 < q` by gvs [PRIME_POS] >>
  `?t. k DIV d = t * q` by gvs [divides_def] >>
  `k = (d * t) * q` by gvs [MULT_ASSOC] >>
  `k DIV q = d * t` by metis_tac[MULT_DIV] >>
  qexists_tac `q` >>
  metis_tac [divides_def, MULT_COMM]
QED



(*Actual lucas primality condition*)
Theorem prime_cert_lucas:
  ∀ n a. 1 < n ∧ a ** (n-1) MOD n = 1 ∧
  ( ∀ q. prime q ∧ q divides (n-1) ⇒  a** ((n-1) DIV q) MOD n ≠ 1)
  ⇒ prime n
Proof
  rpt strip_tac >>
  `0 < n /\ 0 < n - 1` by decide_tac >>
  `ordz n a divides (n - 1)` by gvs [ZN_order_divides_exp] >>
  `0 < ordz n a` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `ordz n a <= n - 1` by gvs [DIVIDES_LE] >>
  `ordz n a = n - 1` by
    (spose_not_then assume_tac >>
     `ordz n a < n - 1` by decide_tac >>
     `?q. prime q /\ q divides (n - 1) /\
        ordz n a divides ((n - 1) DIV q)` by
       gvs [divisor_prime_extension] >>
     `0 < (n - 1) DIV q` by
       metis_tac[DIVIDES_EQN_COMM, MULT_EQ_0, PRIME_POS,
                 NOT_ZERO_LT_ZERO] >>
     metis_tac[ZN_order_divides_exp]) >>
  `phi n < n /\ ordz n a <= phi n` by
    gvs [phi_lt, ZN_order_upper] >>
  irule phi_eq_imp_prime >> decide_tac
QED

Theorem prime_prod_cert:
∀ fs q. EVERY prime fs ∧ prime q ∧ q divides (PROD fs) ⇒ MEM q fs
Proof
Induct >> simp [PROD] >>  rpt strip_tac >>metis_tac [prime_divides_only_self, P_EUCLIDES]
QED

Theorem prime_cert_check:
∀ n a fs. 1 < n ∧ n -1 = PROD fs  ∧
EVERY prime fs  ∧ a** (n-1) MOD n = 1 ∧
EVERY (λq. a** ((n-1) DIV q) MOD n ≠ 1) fs
⇒ prime n
Proof
rpt strip_tac >> match_mp_tac ( Q.SPECL [`n`,`a`] prime_cert_lucas) >>
simp [] >> rpt strip_tac >>  fs [EVERY_MEM]
>> metis_tac [prime_prod_cert, EVERY_MEM ]
QED
