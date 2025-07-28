## `PETA_CONV` {#PairRules.PETA_CONV}


```
PETA_CONV : conv
```



Performs a top-level paired eta-conversion.


`PETA_CONV` maps an eta-redex `\p. t p`, where none of variables in the
paired structure of variables `p` occurs free in `t`,
to the theorem `|- (\p. t p) = t`.

### Failure

Fails if the input term is not a paired eta-redex.
