## `map2`

``` hol4
Lib.map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
```

------------------------------------------------------------------------

Maps a function over two lists to create one new list.

`map2 f [x1,...,xn] [y1,...,yn]` returns `[f x1 y1,...,f xn yn]`.

### Failure

Fails if the two lists are of different lengths. Also fails if any
`f xi yi` fails.

### Example

``` hol4
- map2 (curry op+) [1,2,3] [3,2,1];
> val it = [4, 4, 4] : int list
```

### See also

[`Lib.itlist`](#Lib.itlist), [`Lib.rev_itlist`](#Lib.rev_itlist),
[`Lib.itlist2`](#Lib.itlist2), [`Lib.rev_itlist2`](#Lib.rev_itlist2)
