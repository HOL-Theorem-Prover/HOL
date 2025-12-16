## `PEXISTS_CONV`

``` hol4
PairRules.PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Eliminates paired existential quantifier by introducing a paired
choice-term.

The conversion `PEXISTS_CONV` expects a boolean term of the form
`(?p. t[p])`, where `p` may be a paired structure or variables, and
converts it to the form `(t [@p. t[p]])`.

``` hol4
   ---------------------------------  PEXISTS_CONV "(?p. t[p])"
    (|- (?p. t[p]) = (t [@p. t[p]])
```

### Failure

Fails if applied to a term that is not a paired existential
quantification.

### See also

[`PairRules.PSELECT_RULE`](#PairRules.PSELECT_RULE),
[`PairRules.PSELECT_CONV`](#PairRules.PSELECT_CONV),
[`PairRules.PEXISTS_RULE`](#PairRules.PEXISTS_RULE),
[`PairRules.PSELECT_INTRO`](#PairRules.PSELECT_INTRO),
[`PairRules.PSELECT_ELIM`](#PairRules.PSELECT_ELIM)
