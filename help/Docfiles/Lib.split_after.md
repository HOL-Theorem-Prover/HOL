## `split_after`

``` hol4
Lib.split_after : int -> 'a list -> 'a list * 'a list
```

------------------------------------------------------------------------

Breaks a list in two at a specified index.

An invocation `split_after k [x1,...,xk,...xn]` returns the pair
`([x1,...,xk], [xk+1,...,xn])`. If `k` is `0`, then `split_after k l`
returns `([],l)`. Similarly, `split_after (length l) l` returns
`(l,[])`.

### Failure

If `k` is negative, or longer than the length of the list.

### Example

``` hol4
- split_after 2 [1,2,3,4,5]
> val it = ([1, 2], [3, 4, 5]) : int list * int list

- split_after 0 [1,2,3,4,5];
> val it = ([], [1, 2, 3, 4, 5]) : int list * int list

- split_after 5 [1,2,3,4,5];
> val it = ([1, 2, 3, 4, 5], []) : int list * int list

- split_after 6 [1,2,3,4,5];
! Uncaught exception:
! HOL_ERR

- split_after 0 ([]:int list);
> val it = ([], []) : int list * int list
```

### See also

[`Lib.partition`](#Lib.partition), [`Lib.pluck`](#Lib.pluck)
