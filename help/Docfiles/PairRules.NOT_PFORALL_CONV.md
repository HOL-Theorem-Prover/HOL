## `NOT_PFORALL_CONV`

``` hol4
PairRules.NOT_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Moves negation inwards through a paired universal quantification.

When applied to a term of the form `~(!p. t)`, the conversion
`NOT_PFORALL_CONV` returns the theorem:

``` hol4
   |- ~(!p. t) = (?p. ~t)
```

It is irrelevant whether any variables in `p` occur free in `t`.

### Failure

Fails if applied to a term not of the form `~(!p. t)`.

### See also

[`Conv.NOT_FORALL_CONV`](#Conv.NOT_FORALL_CONV),
[`PairRules.PEXISTS_NOT_CONV`](#PairRules.PEXISTS_NOT_CONV),
[`PairRules.PFORALL_NOT_CONV`](#PairRules.PFORALL_NOT_CONV),
[`PairRules.NOT_PEXISTS_CONV`](#PairRules.NOT_PEXISTS_CONV)
