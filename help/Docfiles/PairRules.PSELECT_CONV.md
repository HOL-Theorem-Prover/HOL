## `PSELECT_CONV`

``` hol4
PairRules.PSELECT_CONV : conv
```

------------------------------------------------------------------------

Eliminates a paired epsilon term by introducing an existential
quantifier.

The conversion `PSELECT_CONV` expects a boolean term of the form
`"t[@p.t[p]/p]"`, which asserts that the epsilon term `@p.t[p]` denotes
a pair, `p` say, for which `t[p]` holds. This assertion is equivalent to
saying that there exists such a pair, and `PSELECT_CONV` applied to a
term of this form returns the theorem `|- t[@p.t[p]/p] = ?p. t[p]`.

### Failure

Fails if applied to a term that is not of the form `"p[@p.t[p]/p]"`.

### See also

[`Conv.SELECT_CONV`](#Conv.SELECT_CONV),
[`PairRules.PSELECT_ELIM`](#PairRules.PSELECT_ELIM),
[`PairRules.PSELECT_INTRO`](#PairRules.PSELECT_INTRO),
[`PairRules.PSELECT_RULE`](#PairRules.PSELECT_RULE)
