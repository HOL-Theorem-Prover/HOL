## `SWAP_PFORALL_CONV`

``` hol4
PairRules.SWAP_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Interchanges the order of two universally quantified pairs.

When applied to a term argument of the form `!p q. t`, the conversion
`SWAP_PFORALL_CONV` returns the theorem:

``` hol4
   |- (!p q. t) = (!q p. t)
```

### Failure

`SWAP_PFORALL_CONV` fails if applied to a term that is not of the form
`!p q. t`.

### See also

[`PairRules.SWAP_PEXISTS_CONV`](#PairRules.SWAP_PEXISTS_CONV)
