## `intersect`

``` hol4
Lib.intersect : ''a list -> ''a list -> ''a list
```

------------------------------------------------------------------------

Computes the intersection of two 'sets'.

`intersect l1 l2` returns a list consisting of those elements of `l1`
that also appear in `l2`.

### Failure

Never fails.

### Example

``` hol4
- intersect [1,2,3] [3,5,4,1];
> val it = [1, 3] : int list
```

### Comments

Do not make the assumption that the order of items in the list returned
by `intersect` is fixed. Later implementations may use different
algorithms, and return a different concrete result while still meeting
the specification.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

ML equality types are used in the implementation of `intersect` and its
kin. This limits its applicability to types that allow equality. For
other types, typically abstract ones, use the 'op\_' variants.

### See also

[`Lib.op_intersect`](#Lib.op_intersect), [`Lib.union`](#Lib.union),
[`Lib.U`](#Lib.U), [`Lib.mk_set`](#Lib.mk_set), [`Lib.mem`](#Lib.mem),
[`Lib.insert`](#Lib.insert), [`Lib.set_eq`](#Lib.set_eq),
[`Lib.set_diff`](#Lib.set_diff)
