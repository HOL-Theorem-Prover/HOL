## `S`

``` hol4
Lib.S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
```

------------------------------------------------------------------------

Generalized function composition: `S f g x` equals `f x (g x)`.

### Failure

`S f` never fails and `S f g` never fails, but `S f g x` fails if `g x`
fails or `f x (g x)` fails.

### See also

[`Lib`](#Lib), [`Lib.##`](#Lib..IAD), [`Lib.C`](#Lib.C),
[`Lib.I`](#Lib.I), [`Lib.K`](#Lib.K), [`Lib.W`](#Lib.W)
