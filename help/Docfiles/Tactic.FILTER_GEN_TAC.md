## `FILTER_GEN_TAC`

``` hol4
Tactic.FILTER_GEN_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Strips off a universal quantifier, but fails for a given quantified
variable.

When applied to a term `s` and a goal `A ?- !x. t`, the tactic
`FILTER_GEN_TAC` fails if the quantified variable `x` is the same as
`s`, but otherwise advances the goal in the same way as `GEN_TAC`,
i.e. returns the goal `A ?- t[x'/x]` where `x'` is a variant of `x`
chosen to avoid clashing with any variables free in the goal's
assumption list. Normally `x'` is just `x`.

``` hol4
     A ?- !x. t
   ==============  FILTER_GEN_TAC "s"
    A ?- t[x'/x]
```

### Failure

Fails if the goal's conclusion is not universally quantified or the
quantified variable is equal to the given term.

### See also

[`Thm.GEN`](#Thm.GEN), [`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`Thm.GENL`](#Thm.GENL), [`Drule.GEN_ALL`](#Drule.GEN_ALL),
[`Thm.SPEC`](#Thm.SPEC), [`Drule.SPECL`](#Drule.SPECL),
[`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC)
