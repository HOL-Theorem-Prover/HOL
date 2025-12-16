## `for`

``` hol4
Lib.for : int -> int -> (int -> 'a) -> 'a list
```

------------------------------------------------------------------------

Functional 'for' loops.

An application `for b t f` is equal to `[f b, f (b+1), ..., f t]`. If
`b` is greater than `t`, the empty list is returned.

### Failure

If `f i` fails for `b <= i <= t`.

### Example

``` hol4
- for 97 122 Char.chr;
> val it =
    [#"a", #"b", #"c", #"d", #"e", #"f", #"g", #"h", #"i", #"j", #"k", #"l",
     #"m", #"n", #"o", #"p", #"q", #"r", #"s", #"t", #"u", #"v", #"w", #"x",
     #"y", #"z"] : char list
```

### See also

[`Lib.for_se`](#Lib.for_se)
