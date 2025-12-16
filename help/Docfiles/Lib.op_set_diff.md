## `op_set_diff`

``` hol4
Lib.op_set_diff : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
```

------------------------------------------------------------------------

Computes the set-theoretic difference of two 'sets', modulo a supplied
relation.

`op_set_diff eq l1 l2` returns a list consisting of those elements of
`l1` that are not `eq` to some element of `l2`.

### Failure

Fails if an application of `eq` fails.

### Example

``` hol4
- op_set_diff (fn x => fn y => x mod 2 = y mod 2) [1,2,3] [4,5,6];
> val it = [] : int list

- op_set_diff (fn x => fn y => x mod 2 = y mod 2) [1,2,3] [2,4,6,8];
> val it = [1, 3] : int list
```

### Comments

The order in which the elements occur in the resulting list should not
be depended upon.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

### See also

[`Lib.set_diff`](#Lib.set_diff), [`Lib.op_mem`](#Lib.op_mem),
[`Lib.op_insert`](#Lib.op_insert), [`Lib.op_union`](#Lib.op_union),
[`Lib.op_U`](#Lib.op_U), [`Lib.op_mk_set`](#Lib.op_mk_set),
[`Lib.op_intersect`](#Lib.op_intersect)
