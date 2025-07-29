## `NOT_PEXISTS_CONV`

``` hol4
PairRules.NOT_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves negation inwards through a paired existential quantification.

When applied to a term of the form `~(?p. t)`, the conversion
`NOT_PEXISTS_CONV` returns the theorem:

``` hol4
   |- ~(?p. t) = (!p. ~t)
```

### Failure

Fails if applied to a term not of the form `~(?p. t)`.

### See also

[`Conv.NOT_EXISTS_CONV`](#Conv.NOT_EXISTS_CONV),
[`PairRules.PEXISTS_NOT_CONV`](#PairRules.PEXISTS_NOT_CONV),
[`PairRules.PFORALL_NOT_CONV`](#PairRules.PFORALL_NOT_CONV),
[`PairRules.NOT_PFORALL_CONV`](#PairRules.NOT_PFORALL_CONV)
