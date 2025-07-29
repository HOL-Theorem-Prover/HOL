## `EXISTS_EQN_CONV`

``` hol4
unwindLib.EXISTS_EQN_CONV : conv
```

------------------------------------------------------------------------

Proves the existence of a line that has a non-recursive equation.

`EXISTS_EQN_CONV "?l. !y1 ... ym. l x1 ... xn = t"` returns the theorem:

``` hol4
   |- (?l. !y1 ... ym. l x1 ... xn = t) = T
```

provided `l` is not free in `t`. Both `m` and `n` may be zero.

### Failure

Fails if the argument term is not of the specified form or if `l`
appears free in `t`.

### See also

[`unwindLib.PRUNE_ONCE_CONV`](#unwindLib.PRUNE_ONCE_CONV)
