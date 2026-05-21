## `U`

``` hol4
Lib.U : ''a list list -> ''a list
```

------------------------------------------------------------------------

Takes the union of a list of sets.

An application `U [l1, ..., ln]` is equivalent to
`union l1 (... (union ln-1, ln)...)`. Thus, every element that occurs in
one of the lists will appear in the result.

### Failure

Never fails.

### Example

``` hol4
- U [[1,2,3], [4,5,6], [1,2,5]];
> val it = [3, 6, 4, 1, 2, 5] : int list
```

### Comments

The order in which the elements occur in the resulting list should not
be depended upon.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

ML equality types are used in the implementation of `U` and its kin.
This limits its applicability to types that allow equality. For other
types, typically abstract ones, use the 'op\_' variants.

### See also

[`Lib.op_U`](#Lib.op_U), [`Lib.union`](#Lib.union),
[`Lib.mk_set`](#Lib.mk_set), [`Lib.mem`](#Lib.mem),
[`Lib.insert`](#Lib.insert), [`Lib.set_eq`](#Lib.set_eq),
[`Lib.intersect`](#Lib.intersect), [`Lib.set_diff`](#Lib.set_diff)
