## `PEXISTS_NOT_CONV`

``` hol4
PairRules.PEXISTS_NOT_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification inwards through a negation.

When applied to a term of the form `?p. ~t`, the conversion
`PEXISTS_NOT_CONV` returns the theorem:

``` hol4
   |- (?p. ~t) = ~(!p. t)
```

### Failure

Fails if applied to a term not of the form `?p. ~t`.

### See also

[`Conv.EXISTS_NOT_CONV`](#Conv.EXISTS_NOT_CONV),
[`PairRules.PFORALL_NOT_CONV`](#PairRules.PFORALL_NOT_CONV),
[`PairRules.NOT_PEXISTS_CONV`](#PairRules.NOT_PEXISTS_CONV),
[`PairRules.NOT_PFORALL_CONV`](#PairRules.NOT_PFORALL_CONV)
