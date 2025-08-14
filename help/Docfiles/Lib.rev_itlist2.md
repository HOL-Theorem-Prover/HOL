## `rev_itlist2`

``` hol4
Lib.rev_itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
```

------------------------------------------------------------------------

Applies a function to corresponding elements of 2 lists.

`rev_itlist2 f [x1,...,xn] [y1,...,yn] z` returns

``` hol4
   f xn yn (f xn-1 yn-1 ... (f x1 y1 z)...)
```

It returns `z` if both lists are empty.

### Failure

Fails if the two lists are of different lengths, or if an application of
`f` raises an exception.

### Example

``` hol4
- rev_itlist2 (fn x => fn y => cons (x,y)) [1,2] [3,4] [];
> val it = [(2, 4), (1, 3)] : (int * int) list
```

### See also

[`Lib.itlist`](#Lib.itlist), [`Lib.rev_itlist`](#Lib.rev_itlist),
[`Lib.itlist2`](#Lib.itlist2), [`Lib.end_itlist`](#Lib.end_itlist)
