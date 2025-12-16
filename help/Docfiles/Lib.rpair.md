## `rpair`

``` hol4
Lib.rpair : 'a -> 'b -> 'b * 'a
```

------------------------------------------------------------------------

Makes two values into a pair, in reverse order.

`rpair x y` returns `(y,x)`.

### Failure

Never fails.

### See also

[`Lib.pair`](#Lib.pair), [`Lib.swap`](#Lib.swap), [`Lib.fst`](#Lib.fst),
[`Lib.snd`](#Lib.snd), [`Lib.curry`](#Lib.curry),
[`Lib.uncurry`](#Lib.uncurry)
