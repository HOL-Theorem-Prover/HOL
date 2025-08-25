## `op_union`

``` hol4
Lib.op_union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
```

------------------------------------------------------------------------

Computes the union of two 'sets'.

If `l1` and `l2` are both 'sets' (lists with no repeated members),
`union eq l1 l2` returns the set union of `l1` and `l2`, using `eq` as
the implementation of element equality. If one or both of `l1` and `l2`
have repeated elements, there may be repeated elements in the result.

### Failure

If some application of `eq` fails.

### Example

``` hol4
- op_union (fn x => fn y => x mod 2 = y mod 2) [1,2,3] [5,4,7];
> val it = [5, 4, 7] : int list
```

### Comments

Do not make the assumption that the order of items in the list returned
by `op_union` is fixed. Later implementations may use different
algorithms, and return a different concrete result while still meeting
the specification.

There is no requirement that `eq` be recognizable as a kind of equality
(it could be implemented by an order relation, for example).

A high-performance implementation of finite sets may be found in
structure `HOLset`.

### See also

[`Lib.union`](#Lib.union), [`Lib.op_mem`](#Lib.op_mem),
[`Lib.op_insert`](#Lib.op_insert), [`Lib.op_mk_set`](#Lib.op_mk_set),
[`Lib.op_U`](#Lib.op_U), [`Lib.op_intersect`](#Lib.op_intersect),
[`Lib.op_set_diff`](#Lib.op_set_diff)
