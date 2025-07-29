## `swap`

``` hol4
Lib.swap : 'a * 'b -> 'b * 'a
```

------------------------------------------------------------------------

Swaps the two components of a pair.

`swap (x,y)` returns `(y,x)`.

### Failure

Never fails.

### See also

[`Lib.fst`](#Lib.fst), [`Lib.snd`](#Lib.snd), [`Lib.pair`](#Lib.pair),
[`Lib.rpair`](#Lib.rpair)
