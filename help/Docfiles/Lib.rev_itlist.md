## `rev_itlist`

``` hol4
Lib.rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
```

------------------------------------------------------------------------

Applies a binary function between adjacent elements of the reverse of a
list.

`rev_itlist f [x1,...,xn] b` returns `f xn ( ... (f x2 (f x1 b))...)`.
It returns `b` if the second argument is an empty list.

### Failure

Fails if some application of `f` fails.

### Example

``` hol4
- rev_itlist (curry op * ) [1,2,3,4] 1;
> val it = 24 : int
```

### See also

[`Lib.itlist`](#Lib.itlist), [`Lib.itlist2`](#Lib.itlist2),
[`Lib.rev_itlist2`](#Lib.rev_itlist2),
[`Lib.end_itlist`](#Lib.end_itlist)
