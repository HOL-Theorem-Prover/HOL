## `insert`

``` hol4
Lib.insert ''a -> ''a list -> ''a list
```

------------------------------------------------------------------------

Add an element to a list if it is not already there.

If `x` is already in `list`, then `insert x list` equals `list`.
Otherwise, `x` becomes an element of `list`.

### Failure

Never fails.

### Example

``` hol4
- insert 1 [3,2];
> val it = [1, 3, 2] : int list

- insert 1 it;
> val it = [1, 3, 2] : int list
```

### Comments

In some programming situations, it is convenient to implement sets by
lists, in which case `insert` may be helpful. However, such an
implementation is only suitable for small sets.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

ML equality types are used in the implementation of `insert` and its
kin. This limits its applicability to types that allow equality. For
other types, typically abstract ones, use the 'op\_' variants.

One should not write code that depends on where the 'list-as-set'
algorithms place elements in the list which is being considered as a
set.

### See also

[`Lib.op_insert`](#Lib.op_insert), [`Lib.mem`](#Lib.mem),
[`Lib.mk_set`](#Lib.mk_set), [`Lib.union`](#Lib.union),
[`Lib.U`](#Lib.U), [`Lib.set_diff`](#Lib.set_diff),
[`Lib.subtract`](#Lib.subtract), [`Lib.intersect`](#Lib.intersect),
[`Lib.null_intersection`](#Lib.null_intersection),
[`Lib.set_eq`](#Lib.set_eq)
