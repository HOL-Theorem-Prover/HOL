## `set_eq`

``` hol4
Lib.set_eq : ''a list -> ''a list -> bool
```

------------------------------------------------------------------------

Tells whether two lists have the same elements.

An application `set_eq l1 l2` returns `true` just in case `l1` and `l2`
are permutations of each other when duplicate elements within each list
are ignored.

### Failure

Never fails.

### Example

``` hol4
- set_eq [1,2,1] [1,2,2,1];
> val it = true : bool

- set_eq [1,2,1] [2,1];
> val it = true : bool
```

### Comments

A high-performance implementation of finite sets may be found in
structure `HOLset`.

ML equality types are used in the implementation of `set_eq` and its
kin. This limits its applicability to types that allow equality. For
other types, typically abstract ones, use the 'op\_' variants.

### See also

[`Lib.intersect`](#Lib.intersect), [`Lib.union`](#Lib.union),
[`Lib.U`](#Lib.U), [`Lib.mk_set`](#Lib.mk_set), [`Lib.mem`](#Lib.mem),
[`Lib.insert`](#Lib.insert), [`Lib.set_diff`](#Lib.set_diff)
