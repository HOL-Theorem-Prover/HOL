## `itlist`

``` hol4
Lib.itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
```

------------------------------------------------------------------------

List iteration function. Applies a binary function between adjacent
elements of a list.

`itlist f [x1,...,xn] b` returns

``` hol4
   f x1 (f x2 ... (f xn b)...)
```

An invocation `itlist f list b` returns `b` if `list` is empty.

### Failure

Fails if some application of `f` fails.

### Example

``` hol4
- itlist (curry op+) [1,2,3,4] 0;
val it = 10 : int
```

### See also

[`Lib.itlist2`](#Lib.itlist2), [`Lib.rev_itlist`](#Lib.rev_itlist),
[`Lib.rev_itlist2`](#Lib.rev_itlist2),
[`Lib.end_itlist`](#Lib.end_itlist)
