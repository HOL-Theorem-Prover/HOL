signature QbfConv = sig
  type conv = Abbrev.conv

  (* put an arbitrary QBF into the required form *)
  (* specifically,
     input term:
       - has type bool
       - is closed
       - contains only:
         - first order connectives (/\,\/,==>,~)
            (TODO: allow equality?)
         - quantifiers (!,?)
         - variables
     output term:
       - of the form Q_1 x_1. ... Q_n x_n. phi
       - each Q_i is either ! or ?
       - Q_n is ?
       - each x_i appears in phi
       - phi is closed and in CNF
     alternatively, the output term might simply be 'T' or 'F'
  *)
  val qbf_prenex_conv : conv

  (* simplifies clauses (specialisation of SIMP_CONV). In particular, does the following rewrites:
    (∀x. x ∨ P) = P, (∀x. ¬x ∨ P) = P, (∀x. x) = F, (∀x. ¬x) = F,
    and associativity/commutativity normalisation for conjunction and disjunction *)
  val simp_clauses : conv

  (* conversion that takes [!x:bool. t] where t is in CNF and may contain x and
  removes the quantifier and all occurrences of x. also simplifies clauses (as above). *)
  val remove_forall : conv

  (* [last_quant_conv c] strips a quantifier (! and ? only) prefix down
     to the last quantifier then applies c to the (singly quantified) body *)
  val last_quant_conv : conv -> conv

  (* applies a conversion under a quantifier prefix of foralls and exists *)
  val strip_prefix_conv : conv -> conv

  (* [last_quant_seq_conv cq cb] applies cb under the quantifier prefix and
    then cq before each quantifier. That is:
      Q1 x1. Q2 x2. ... Qn xn. P --> cq (Q1 x1. cq (Q2 x2. ... cq (Qn. xn. cb P))))
  *)
  val last_quant_seq_conv : conv -> conv -> conv

  (* applies cb under the quantifier prefix, and then, if the innermost
    quantifiers are all universal, applies cq before each of them *)
  val last_forall_seq_conv : conv -> conv -> conv

end
