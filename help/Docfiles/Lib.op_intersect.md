## `op_intersect`

``` hol4
Lib.op_intersect : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
```

------------------------------------------------------------------------

Computes the intersection of two 'sets'.

`op_intersect eq l1 l2` returns a list consisting of those elements of
`l1` that are `eq` to some element in `l2`.

### Failure

Fails if an application of `eq` fails.

### Example

``` hol4
- op_intersect aconv [Term `\x:bool.x`, Term `\x y. x /\ y`]
                     [Term `\y:bool.y`, Term `\x y. x /\ z`];
> val it = [`\x. x`] : term list
```

### Comments

The order of items in the list returned by `op_intersect` is not
dependable.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

There is no requirement that `eq` be recognizable as a kind of equality
(it could be implemented by an order relation, for example).

### See also

[`Lib.intersect`](#Lib.intersect), [`Lib.op_mem`](#Lib.op_mem),
[`Lib.op_insert`](#Lib.op_insert), [`Lib.op_mk_set`](#Lib.op_mk_set),
[`Lib.op_union`](#Lib.op_union), [`Lib.op_U`](#Lib.op_U),
[`Lib.op_set_diff`](#Lib.op_set_diff)
