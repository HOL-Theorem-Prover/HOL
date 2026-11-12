(* -------------------------------------------------------------------------
   Kernel computation equations for certificate arithmetic

   Documentation
   Computational views of GF addition/multiplication, without unfolding
   the full field record. Modular exponentiation is provided by the shared
   expMod theory and the standard CV translations, not a private program.

   Public interface
   - certificate_gf_add and certificate_gf_mult expose numeric GF operations.

   certificateComputeLib uses these proved equations for conversions;
   evaluating candidate arithmetic is not an additional oracle.
   ------------------------------------------------------------------------- *)

Theory certificateCompute
Ancestors
  arithmetic fieldInstances

(* Functional equations expose closures before CBV traverses the arguments of
   a neutral record selector.  This matters for large field coefficients. *)
Theorem certificate_gf_add:
  !(p:num). (GF p).sum.op = \x y. (x + y) MOD p
Proof
  SIMP_TAC bool_ss [FUN_EQ_THM, GF_add]
QED

Theorem certificate_gf_mult:
  !(p:num). (GF p).prod.op = \x y. (x * y) MOD p
Proof
  SIMP_TAC bool_ss [FUN_EQ_THM, GF_mult]
QED
