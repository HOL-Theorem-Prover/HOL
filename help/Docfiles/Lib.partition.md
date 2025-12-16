## `partition`

``` hol4
Lib.partition : ('a -> bool) -> 'a list -> 'a list * 'a list
```

------------------------------------------------------------------------

Split a list by a predicate.

An invocation `partition P l` divides `l` into a pair of lists
`(l1,l2)`. `P` holds of each element of `l1`, and `P` does not hold of
any element of `l2`.

### Failure

If applying `P` to any element of `l` results in failure.

### Example

``` hol4
- partition (fn i => i mod 2 = 0) [1,2,3,4,5,6,7,8,9];
> val it = ([2, 4, 6, 8], [1, 3, 5, 7, 9]) : int list * int list

- partition (fn _ => true) [1,2,3];
> val it = ([1, 2, 3], []) : int list * int list

- partition (fn _ => raise Fail "") ([]:int list);
> val it = ([], []) : int list * int list

- partition (fn _ => raise Fail "") [1];
! Uncaught exception:
! Fail  ""
```

### See also

[`Lib.split_after`](#Lib.split_after), [`Lib.pluck`](#Lib.pluck)
