
(* ------------------------------------------------------------------------- *)
(* Theory: Pedersen Commitment Scheme                                        *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib Parse;
open numTheory jcLib monoidTheory fieldTheory fieldInstancesTheory;
open groupTheory arithmeticTheory dividesTheory numeralTheory ringTheory;

(* Declare new theory at start *)
val _ = new_theory "pedersenCommitment";

(* Overload operations to avoid ambiguity *)
Overload "_0_" = “(GF q).sum.id”;
Overload "_1_" = “(GF q).prod.id”;
Overload "_+_" = “(GF q).sum.op”; val _ = set_fixity "_+_" (Infixl 500);
Overload "_-_" = “ring_sub (GF q)”; val _ = set_fixity "_-_" (Infixl 500);
Overload "_*_" = “(GF q).prod.op”; val _ = set_fixity "_*_" (Infixl 600);
Overload "_/_" = “field_div (GF q)”; val _ = set_fixity "_/_" (Infixl 600);

(* Theorems *)

val field_mult_solve_eqn = store_thm(
  "field_mult_solve_eqn",
  “!r:'a field. Field r ==>
       !x y z. x IN R /\ y IN R /\ z IN R /\ y <> #0 ==>
               (x = z * y <=> x / y = z)”,
  rw[EQ_IMP_THM] >-
   (simp[field_nonzero_eq, field_mult_assoc, field_mult_rinv]) >>
   simp[field_nonzero_eq, field_mult_assoc, field_mult_linv]);

val GF_mult_solve_eqn = store_thm(
  "GF_mult_solve_eqn",
  “!q. prime q ==>
      !d m i. m IN (GF q).carrier /\
              d IN (GF q).carrier /\
              i IN (GF q).carrier /\ m <> _0_ ==>
              (d = i _*_ m <=>  d _/_ m = i)”,
  simp[GF_field, field_mult_solve_eqn]);

val GF_sub_not_eq_zero = store_thm(
  "GF_sub_not_eq_zero",
  “∀q. prime q ⇒
       ∀m1 m2.
         m1 IN (GF q).carrier ∧
         m2 IN (GF q).carrier ∧
         m2 ≠ m1 ⇒
         m2 _-_ m1 ≠ _0_”,
  rpt strip_tac >>
  ‘Field (GF q)’ by rw[GF_field] >>
  metis_tac[field_sub_eq_zero]);

val GF_mult_rsub = store_thm(
  "GF_mult_rsub",
  “∀q. prime q ⇒
       ∀m1 m2 i.
         m1 IN (GF q).carrier ∧
         m2 IN (GF q).carrier ∧
         i IN (GF q).carrier ⇒
         (i _*_ m2) _-_ (i _*_ m1) = i _*_ (m2 _-_ m1)”,
  rpt strip_tac >>
  ‘Field (GF q)’ by rw[GF_field] >>
  metis_tac[field_mult_rsub]);

Theorem field_mult_not_zero:
  !r:'a field.
    Field r  ==>
    !d m i. d IN R ∧ m IN R ∧ i IN R ∧ d = i * m ∧ i ≠ #0 ∧ m ≠ #0 ==> (d ≠ #0)
Proof
  rpt strip_tac >>
  rw[] >>
  ‘i = #0 ∨ m = #0’ by metis_tac[field_mult_eq_zero]
QED

val GF_mult_not_zero = store_thm(
  "GF_mult_not_zero",
  “∀q. prime q ⇒
       ∀d m i.
         m IN (GF q).carrier ∧
         d IN (GF q).carrier ∧
         i IN (GF q).carrier ∧
         d = i _*_ m ∧
         i ≠  _0_ ∧
         m ≠  _0_   ⇒ d ≠ _0_”,
  rpt strip_tac >>
  ‘Field (GF q)’ by rw[GF_field] >>
  metis_tac[field_mult_not_zero]);

val GF_add_sub_identity = store_thm(
  "GF_add_sub_identity",
  “∀q. prime q ⇒
       ∀x y z t.
         x IN (GF q).carrier ∧
         y IN (GF q).carrier ∧
         z IN (GF q).carrier ∧
         t IN (GF q).carrier ∧
         x _+_ y = z _+_ t ⇒
         x _-_ z = t _-_ y”,
  rpt strip_tac >>
  ‘Field (GF q)’ by metis_tac[GF_field] >>
  metis_tac[field_add_sub_identity]);

val GF_diff_mult_solve = store_thm(
  "GF_diff_mult_solve",
  “∀q. prime q ⇒
       ∀d1 d2 m1 m2 i.
         d1 IN (GF q).carrier ∧
         d2 IN (GF q).carrier ∧
         m1 IN (GF q).carrier ∧
         m2 IN (GF q).carrier ∧
         i IN (GF q).carrier ∧
         m2 ≠ m1 ∧
         d1 _-_ d2 = i _*_ (m2 _-_ m1) ⇒
         (d1 _-_ d2) _/_ (m2 _-_ m1) = i”,
  rpt strip_tac >>
  ‘Field (GF q)’ by rw[GF_field] >>
  ‘m2 _-_ m1 ≠ _0_’ by metis_tac[GF_sub_not_eq_zero] >>
  ‘(d1 _-_ d2) IN (GF q).carrier ∧ (m2 _-_ m1) IN (GF q).carrier’ by rw[] >>
  metis_tac[GF_mult_solve_eqn]);

(* Definitions *)
Definition commit_def:
  commit (g: 'a group) (h: 'a) d k m = g.op (monoid_exp g h d) (monoid_exp g k m)
End

Definition verify_def:
  verify (g: 'a group) (h: 'a) c d k m ⇔ commit g h d k m = c
End

(* Theorems involving commit and verify *)
val GF_pedersen_binding = store_thm(
  "GF_pedersen_binding",
  “∀q. prime q ⇒
       ∀m1 m2 d1 d2.
         m1 IN (GF q).carrier ∧
         m2 IN (GF q).carrier ∧
         d1 IN (GF q).carrier ∧
         d2 IN (GF q).carrier ∧
         (m1 ≠ m2) ⇒
            ∀g: 'a group. cyclic g ∧ FINITE G ∧  (ord (cyclic_gen g) = q) ⇒
                  ∀k. k IN G ∧
                      verify g (cyclic_gen g) (commit g (cyclic_gen g) d1 k m1) d2 k m2
                                            ⇒
                     (d1 _-_ d2) _/_ (m2 _-_ m1) = cyclic_index g k”,
  simp[commit_def, verify_def, Excl "ring_sub_def", Excl "field_div_def"] >>
  rpt strip_tac >>
  qabbrev_tac ‘h = cyclic_gen g’ >>
  ‘Group g’ by metis_tac[cyclic_def] >>
  ‘cyclic_gen g IN G’ by metis_tac[cyclic_gen_element] >>
  ‘(ord (cyclic_gen g)) = CARD G’ by metis_tac[cyclic_gen_order] >>
  ‘∃i. i < q ∧ k = monoid_exp g h i’ by metis_tac[cyclic_element_by_gen] >>
  ‘cyclic_index g k = i’ by metis_tac[finite_cyclic_index_unique] >>
  ‘h IN G’ by fs[cyclic_gen_element, Abbr`h`] >>
  ‘i IN (GF q).carrier’ by rw[GF_eval] >>
  fs[GSYM group_exp_mult, Excl "monoid_exp_mult", GSYM group_exp_add, Excl "monoid_exp_add",
     Excl "ring_sub_def", Excl "field_div_def"] >>
  ‘0 < q’ by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
  ‘monoid_exp g h ((d2 + i * m2) MOD q) = monoid_exp g h ((d1 + i * m1) MOD q)’ by metis_tac[group_exp_mod] >>
  qabbrev_tac ‘x2 = monoid_exp g h ((d2 + i * m2) MOD q)’ >>
  qabbrev_tac ‘x1 = monoid_exp g h ((d1 + i * m1) MOD q)’ >>
  ‘x2 IN G ∧ x1 IN G’ by fs[Abbr`x2`, Abbr`x1`] >>
  ‘((d2 + i * m2) MOD q) = cyclic_index g x2 ∧ ((d1 + i * m1) MOD q) = cyclic_index g x1’
     by metis_tac[finite_cyclic_index_unique, MOD_LESS] >>
  ‘((d2 + i * m2) MOD q) = ((d1 + i * m1) MOD q)’ by rw[] >>
  ‘d2 _+_ i _*_ m2 = d1 _+_ i _*_ m1’ by metis_tac[MOD_PLUS, MOD_MOD, GF_eval] >>
  ‘Field (GF q)’ by rw[GF_field] >>
  ‘d1 _-_ d2 = (i _*_ m2) _-_ (i _*_ m1)’ by rw[GF_add_sub_identity, GF_eval] >>
  ‘d1 _-_ d2 = i _*_ (m2 _-_ m1)’ by rw[GF_mult_rsub, GF_eval] >>
  prove_tac[GF_diff_mult_solve]);

Theorem GF_pedersen_binding_prime = GF_pedersen_binding |> SIMP_RULE (srw_ss()) [verify_def];

val GF_pedersen_hiding = store_thm(
  "GF_pedersen_hiding",
  “∀q. prime q ⇒
       ∀m. m IN (GF q).carrier ⇒
           ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q) ⇒
                         ∀c k. c IN G ∧ k IN G  ⇒
                               ∃d. d IN (GF q).carrier ∧
                                   c = commit g (cyclic_gen g) d k m”,
  simp[commit_def] >>
  rw[] >>
  ‘∃i. i < CARD G ∧ c = monoid_exp g (cyclic_gen g) i’ by rw[cyclic_element_by_gen] >>
  ‘∃j. j < CARD G ∧ k = monoid_exp g (cyclic_gen g) j’ by rw[cyclic_element_by_gen] >>
  ‘Group g’ by metis_tac[cyclic_def] >>
  rw[Once EQ_SYM_EQ] >>
  rw[group_lsolve, cyclic_gen_element, cyclic_gen_order] >>
  ‘monoid_exp g (monoid_exp g (cyclic_gen g) j) m IN G’ by rw[] >>
  ‘monoid_inv g (monoid_exp g (monoid_exp g (cyclic_gen g) j) m) IN G’ by rw[group_inv_element] >>
  ‘(g.op (monoid_exp g (cyclic_gen g) i) (monoid_inv g (monoid_exp g (monoid_exp g (cyclic_gen g) j) m))) IN G’
     by rw[group_op_element] >>
  qabbrev_tac ‘x = (g.op (monoid_exp g (cyclic_gen g) i) (monoid_inv g (monoid_exp g (monoid_exp g (cyclic_gen g) j) m)))’ >>
  ‘∃d. d < CARD G ∧ x = monoid_exp g (cyclic_gen g) d’ by rw[cyclic_element_by_gen] >>
  ‘ord (cyclic_gen g) = CARD G’ by rw[cyclic_gen_order] >>
  ‘d ∈ (GF (CARD G)).carrier’ by rw[GF_eval] >>
  qexists_tac ‘d’ >>
  rw[]);

val ZN_pedersen_hiding = store_thm(
  "ZN_pedersen_hiding",
  “∀q. prime q ⇒
       ∀m. m IN (ZN q).carrier ⇒
           ∀g: 'a group. cyclic g ∧ FINITE G ∧ (ord (cyclic_gen g) = q) ⇒
                         ∀c k. c IN G ∧ k IN G  ⇒
                               ∃d. d IN (ZN q).carrier ∧
                                   c = commit g (cyclic_gen g) d k m”,
  simp[commit_def] >>
  rw[] >>
  ‘∃i. i < CARD G ∧ c = monoid_exp g (cyclic_gen g) i’ by rw[cyclic_element_by_gen] >>
  ‘∃j. j < CARD G ∧ k = monoid_exp g (cyclic_gen g) j’ by rw[cyclic_element_by_gen] >>
  ‘Group g’ by metis_tac[cyclic_def] >>
  rw[Once EQ_SYM_EQ] >>
  rw[ZN_def] >>
  rw[cyclic_gen_order] >>
  rw[group_lsolve, cyclic_gen_element, cyclic_gen_order] >>
  rw[Once EQ_SYM_EQ] >>
  irule cyclic_element_by_gen >>
  simp[]);

Theorem GF_pedersen_hiding_prime = GF_pedersen_hiding |> SIMP_RULE (srw_ss()) [verify_def];

val _ = export_theory();
