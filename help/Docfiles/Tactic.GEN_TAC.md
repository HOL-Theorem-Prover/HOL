## `GEN_TAC`

``` hol4
Tactic.GEN_TAC : tactic
```

------------------------------------------------------------------------

Strips the outermost universal quantifier from the conclusion of a goal.

When applied to a goal `A ?- !x. t`, the tactic `GEN_TAC` reduces it to
`A ?- t[x'/x]` where `x'` is a variant of `x` chosen to avoid clashing
with any variables free in the goal's assumption list. Normally `x'` is
just `x`.

``` hol4
     A ?- !x. t
   ==============  GEN_TAC
    A ?- t[x'/x]
```

### Failure

Fails unless the goal's conclusion is universally quantified.

The tactic `REPEAT GEN_TAC` strips away any universal quantifiers, and
is commonly used before tactics relying on the underlying term
structure.

### See also

[`Tactic.FILTER_GEN_TAC`](#Tactic.FILTER_GEN_TAC),
[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL),
[`Drule.GEN_ALL`](#Drule.GEN_ALL), [`Thm.SPEC`](#Thm.SPEC),
[`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Tactic.X_GEN_TAC`](#Tactic.X_GEN_TAC)
