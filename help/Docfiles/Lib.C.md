## `C`

``` hol4
Lib.C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
```

------------------------------------------------------------------------

Permutes first two arguments to curried function: `C f x y` equals
`f y x`.

### Failure

`C f` never fails and `C f x` never fails, but `C f x y` fails if
`f y x` fails.

### Example

``` hol4
- map (C cons []) [1,2,3];
> val it = [[1], [2], [3]] : int list list
```

### See also

[`Lib.##`](#Lib..IAD), [`Lib.I`](#Lib.I), [`Lib.K`](#Lib.K),
[`Lib.S`](#Lib.S), [`Lib.W`](#Lib.W)
