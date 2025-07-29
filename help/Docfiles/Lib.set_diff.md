## `set_diff`

``` hol4
Lib.set_diff : ''a list -> ''a list -> ''a list
```

------------------------------------------------------------------------

Computes the set-theoretic difference of two 'sets'.

`set_diff l1 l2` returns a list consisting of those elements of `l1`
that do not appear in `l2`. It is identical to `Lib.subtract`.

### Failure

Never fails.

### Example

``` hol4
- set_diff [] [1,2];
> val it = [] : int list

- set_diff [1,2,3] [2,1];
> val it = [3] : int list
```

### Comments

The order in which the elements occur in the resulting list should not
be depended upon.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

ML equality types are used in the implementation of `union` and its kin.
This limits its applicability to types that allow equality. For other
types, typically abstract ones, use the 'op\_' variants.

### See also

[`Lib.op_set_diff`](#Lib.op_set_diff), [`Lib.subtract`](#Lib.subtract),
[`Lib.mk_set`](#Lib.mk_set), [`Lib.set_eq`](#Lib.set_eq),
[`Lib.union`](#Lib.union), [`Lib.intersect`](#Lib.intersect)
