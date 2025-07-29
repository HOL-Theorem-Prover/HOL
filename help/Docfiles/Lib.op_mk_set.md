## `op_mk_set`

``` hol4
Lib.op_mk_set : ('a -> 'a -> bool) -> 'a list -> 'a list
```

------------------------------------------------------------------------

Transforms a list into one with elements that are distinct modulo the
supplied relation.

An invocation `op_mk_set eq list` returns a list consisting of the
`eq`-distinct members of `list`. In particular, the result list will not
contain elements `x` and `y` at different positions such that `eq x y`
evaluates to `true`.

### Failure

If an application of `eq` fails when applied to two elements of `list`.

### Example

``` hol4
- op_mk_set aconv [Term `\x y. x /\ y`,
                   Term `\y x. y /\ x`,
                   Term `\z a. z /\ a`];
> val it = [`\z a. z /\ a`] : term list
```

### Comments

The order of items in the list returned by `op_mk_set` is not
dependable.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

There is no requirement that `eq` be recognizable as a kind of equality
(it could be implemented by an order relation, for example).

### See also

[`Lib.mk_set`](#Lib.mk_set), [`Lib.op_mem`](#Lib.op_mem),
[`Lib.op_insert`](#Lib.op_insert), [`Lib.op_union`](#Lib.op_union),
[`Lib.op_U`](#Lib.op_U), [`Lib.op_intersect`](#Lib.op_intersect),
[`Lib.op_set_diff`](#Lib.op_set_diff)
