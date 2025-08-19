## `union`

``` hol4
Lib.union : ''a list -> ''a list -> ''a list
```

------------------------------------------------------------------------

Computes the union of two 'sets'.

If `l1` and `l2` are both 'sets' (lists with no repeated members),
`union l1 l2` returns the set union of `l1` and `l2`. In the case that
`l1` or `l2` is not a set, all the user can depend on is that
`union l1 l2` returns a list `l3` such that every unique element of `l1`
and `l2` is in `l3` and each element of `l3` is found in either `l1` or
`l2`.

### Failure

Never fails.

### Example

``` hol4
- union [1,2,3] [1,5,4,3];
val it = [2,1,5,4,3] : int list

- union [1,1,1] [1,2,3,2];
val it = [1,2,3,2] : int list

- union [1,2,3,2] [1,1,1] ;
val it = [3,2,1,1,1] : int list
```

### Comments

Do not make the assumption that the order of items in the list returned
by `union` is fixed. Later implementations may use different algorithms,
and return a different concrete result while still meeting the
specification.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

ML equality types are used in the implementation of `union` and its kin.
This limits its applicability to types that allow equality. For other
types, typically abstract ones, use the 'op\_' variants.

### See also

[`Lib.op_union`](#Lib.op_union), [`Lib.U`](#Lib.U),
[`Lib.mk_set`](#Lib.mk_set), [`Lib.mem`](#Lib.mem),
[`Lib.insert`](#Lib.insert), [`Lib.set_eq`](#Lib.set_eq),
[`Lib.intersect`](#Lib.intersect), [`Lib.set_diff`](#Lib.set_diff),
[`Lib.subtract`](#Lib.subtract)
