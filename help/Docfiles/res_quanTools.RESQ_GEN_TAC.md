## `RESQ_GEN_TAC`

``` hol4
res_quanTools.RESQ_GEN_TAC : tactic
```

------------------------------------------------------------------------

Strips the outermost restricted universal quantifier from the conclusion
of a goal.

When applied to a goal `A ?- !x::P. t`, the tactic `RESQ_GEN_TAC`
reduces it to a new goal `A,P x' ?- t[x'/x]` where `x'` is a variant of
`x` chosen to avoid clashing with any variables free in the goal's
assumption list. Normally `x'` is just `x`.

``` hol4
     A ?- !x::P. t
   ===================  RESQ_GEN_TAC
    A,P x' ?- t[x'/x]
```

### Failure

Fails unless the goal's conclusion is a restricted universal
quantification.

The tactic `REPEAT RESQ_GEN_TAC` strips away a series of restricted
universal quantifiers, and is commonly used before tactics relying on
the underlying term structure.

### See also

[`res_quanTools.RESQ_SPEC`](#res_quanTools.RESQ_SPEC),
[`res_quanTools.RESQ_SPECL`](#res_quanTools.RESQ_SPECL),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`Tactic.X_GEN_TAC`](#Tactic.X_GEN_TAC)
