## `EXISTS_DEL1_CONV`

``` hol4
unwindLib.EXISTS_DEL1_CONV : conv
```

------------------------------------------------------------------------

Deletes one existential quantifier.

`EXISTS_DEL1_CONV "?x. t"` returns the theorem:

``` hol4
   |- (?x. t) = t
```

provided `x` is not free in `t`.

### Failure

Fails if the argument term is not an existential quantification or if
`x` is free in `t`.

### See also

[`unwindLib.EXISTS_DEL_CONV`](#unwindLib.EXISTS_DEL_CONV),
[`unwindLib.PRUNE_ONCE_CONV`](#unwindLib.PRUNE_ONCE_CONV)
