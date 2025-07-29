## `PFORALL_NOT_CONV`

``` hol4
PairRules.PFORALL_NOT_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification inwards through a negation.

When applied to a term of the form `!p. ~t`, the conversion
`PFORALL_NOT_CONV` returns the theorem:

``` hol4
   |- (!p. ~t) = ~(?p. t)
```

### Failure

Fails if applied to a term not of the form `!p. ~t`.

### See also

[`Conv.FORALL_NOT_CONV`](#Conv.FORALL_NOT_CONV),
[`PairRules.PEXISTS_NOT_CONV`](#PairRules.PEXISTS_NOT_CONV),
[`PairRules.NOT_PEXISTS_CONV`](#PairRules.NOT_PEXISTS_CONV),
[`PairRules.NOT_PFORALL_CONV`](#PairRules.NOT_PFORALL_CONV)
