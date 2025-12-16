## `EXISTS_DEL_CONV`

``` hol4
unwindLib.EXISTS_DEL_CONV : conv
```

------------------------------------------------------------------------

Deletes existential quantifiers.

`EXISTS_DEL_CONV "?x1 ... xn. t"` returns the theorem:

``` hol4
   |- (?x1 ... xn. t) = t
```

provided `x1,...,xn` are not free in `t`.

### Failure

Fails if any of the `x`'s appear free in `t`. The function does not
perform a partial deletion; for example, if `x1` and `x2` do not appear
free in `t` but `x3` does, the function will fail; it will not return:

``` hol4
   |- ?x1 ... xn. t = ?x3 ... xn. t
```

### See also

[`unwindLib.EXISTS_DEL1_CONV`](#unwindLib.EXISTS_DEL1_CONV),
[`unwindLib.PRUNE_CONV`](#unwindLib.PRUNE_CONV)
