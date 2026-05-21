## `null_intersection`

``` hol4
Lib.null_intersection : ''a list -> ''a list -> bool
```

------------------------------------------------------------------------

Tells if two lists have no common elements.

An invocation `null_intersection l1 l2` is equivalent to
`null(intersect l1 l2)`, but is more efficient in the case where the
intersection is not empty.

### Failure

Never fails.

### Example

``` hol4
- null_intersection [1,2,3,4] [5,6,7,8];
> val it = true : bool

- null_intersection [1,2,3,4] [8,5,3];
> val it = false : bool
```

### Comments

A high-performance implementation of finite sets may be found in
structure `HOLset`.

### See also

[`Lib.intersect`](#Lib.intersect), [`Lib.union`](#Lib.union),
[`Lib.U`](#Lib.U), [`Lib.mk_set`](#Lib.mk_set), [`Lib.mem`](#Lib.mem),
[`Lib.insert`](#Lib.insert), [`Lib.set_eq`](#Lib.set_eq),
[`Lib.set_diff`](#Lib.set_diff)
