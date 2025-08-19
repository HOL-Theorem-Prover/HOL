## `itlist2`

``` hol4
Lib.itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
```

------------------------------------------------------------------------

Applies a function to corresponding elements of 2 lists.

`itlist2 f [x1,...,xn] [y1,...,yn] z` returns

``` hol4
   f x1 y1 (f x2 y2 ... (f xn yn z)...)
```

An invocation `itlist2 f list1 list2 b` returns `b` if `list1` and
`list2` are empty.

### Failure

Fails if the two lists are of different lengths, or if one of the
applications of `f` fails.

### Example

``` hol4
- itlist2 (fn x => fn y => fn z => (x,y)::z) [1,2] [3,4] [];
> val it = [(1,3), (2,4)] : (int * int) list
```

### See also

[`Lib.itlist`](#Lib.itlist), [`Lib.rev_itlist`](#Lib.rev_itlist),
[`Lib.rev_itlist2`](#Lib.rev_itlist2),
[`Lib.end_itlist`](#Lib.end_itlist)
