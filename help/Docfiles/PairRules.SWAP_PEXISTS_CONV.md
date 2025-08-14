## `SWAP_PEXISTS_CONV`

``` hol4
PairRules.SWAP_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Interchanges the order of two existentially quantified pairs.

When applied to a term argument of the form `?p q. t`, the conversion
`SWAP_PEXISTS_CONV` returns the theorem:

``` hol4
   |- (?p q. t) = (?q t. t)
```

### Failure

`SWAP_PEXISTS_CONV` fails if applied to a term that is not of the form
`?p q. t`.

### See also

[`Conv.SWAP_EXISTS_CONV`](#Conv.SWAP_EXISTS_CONV),
[`PairRules.SWAP_PFORALL_CONV`](#PairRules.SWAP_PFORALL_CONV)
