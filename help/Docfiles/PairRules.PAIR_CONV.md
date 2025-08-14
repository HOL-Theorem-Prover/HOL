## `PAIR_CONV`

``` hol4
PairRules.PAIR_CONV : (conv -> conv)
```

------------------------------------------------------------------------

Applies a conversion to all the components of a pair structure.

For any conversion `c`, the function returned by `PAIR_CONV c` is a
conversion that applies `c` to all the components of a pair. If the term
`t` is not a pair, them `PAIR_CONV c t` applies `c` to `t`. If the term
`t` is the pair `(t1,t2)` then `PAIR c t` recursively applies
`PAIR_CONV c` to `t1` and `t2`.

### Failure

The conversion returned by `PAIR_CONV c` will fail for the pair
structure `t` if the conversion `c` would fail for any of the components
of `t`.

### See also

[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV)
