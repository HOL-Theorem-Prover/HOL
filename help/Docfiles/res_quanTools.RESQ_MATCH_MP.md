## `RESQ_MATCH_MP`

``` hol4
res_quanTools.RESQ_MATCH_MP : (thm -> thm -> thm)
```

------------------------------------------------------------------------

Eliminating a restricted universal quantification with automatic
matching.

When applied to theorems `A1 |- !x::P. Q[x]` and `A2 |- P x'`, the
derived inference rule `RESQ_MATCH_MP` matches `x'` to `x` by
instantiating free or universally quantified variables in the first
theorem (only), and returns a theorem `A1 u A2 |- Q[x'/x]`. Polymorphic
types are also instantiated if necessary.

``` hol4
    A1 |- !x::P.Q[x]   A2 |- P x'
   --------------------------------------  RESQ_MATCH_MP
          A1 u A2 |- Q[x'/x]
```

### Failure

Fails unless the first theorem is a (possibly repeatedly) restricted
universal quantification whose quantified variable can be instantiated
to match the conclusion of the second theorem, without instantiating any
variables which are free in `A1`, the first theorem's assumption list.

### See also

[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`res_quanTools.RESQ_HALF_SPEC`](#res_quanTools.RESQ_HALF_SPEC)
