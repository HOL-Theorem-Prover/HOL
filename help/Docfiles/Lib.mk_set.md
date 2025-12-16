## `mk_set`

``` hol4
Lib.mk_set : ''a list -> ''a list
```

------------------------------------------------------------------------

Transforms a list into one with distinct elements.

An invocation `mk_set list` returns a list consisting of the distinct
members of `list`. In particular, the result list has no repeated
elements.

### Failure

Never fails.

### Example

``` hol4
- mk_set [1,1,1,2,2,2,3,3,4];
> val it = [1, 2, 3, 4] : int list
```

### Comments

In some programming situations, it is convenient to implement sets by
lists, in which case `mk_set` may be helpful. However, such an
implementation is only suitable for small sets.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

ML equality types are used in the implementation of `mk_set` and its
kin. This limits its applicability to types that allow equality. For
other types, typically abstract ones, use the 'op\_' variants.

### See also

[`Lib.op_mk_set`](#Lib.op_mk_set), [`Lib.mem`](#Lib.mem),
[`Lib.insert`](#Lib.insert), [`Lib.union`](#Lib.union),
[`Lib.U`](#Lib.U), [`Lib.set_diff`](#Lib.set_diff),
[`Lib.subtract`](#Lib.subtract), [`Lib.intersect`](#Lib.intersect),
[`Lib.null_intersection`](#Lib.null_intersection),
[`Lib.set_eq`](#Lib.set_eq)
