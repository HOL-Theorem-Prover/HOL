## `op_mem`

``` hol4
Lib.op_mem : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
```

------------------------------------------------------------------------

Tests whether a list contains a certain element.

An invocation `op_mem eq x [x1,...,xn]` returns `true` if, for some `xi`
in the list, `eq xi x` evaluates to `true`. Otherwise it returns
`false`.

### Failure

Only fails if an application of `eq` fails.

### Example

``` hol4
- op_mem aconv (Term `\x. x /\ y`) [T, Term `\z. z /\ y`, F];
> val it = true : bool
```

### Comments

A high-performance implementation of finite sets may be found in
structure `HOLset`.

### See also

[`Lib.mem`](#Lib.mem), [`Lib.op_insert`](#Lib.op_insert),
[`Lib.tryfind`](#Lib.tryfind), [`Lib.exists`](#Lib.exists),
[`Lib.all`](#Lib.all), [`Lib.assoc`](#Lib.assoc),
[`Lib.rev_assoc`](#Lib.rev_assoc), [`Lib.assoc1`](#Lib.assoc1),
[`Lib.assoc2`](#Lib.assoc2), [`Lib.op_union`](#Lib.op_union),
[`Lib.op_mk_set`](#Lib.op_mk_set), [`Lib.op_U`](#Lib.op_U),
[`Lib.op_intersect`](#Lib.op_intersect),
[`Lib.op_set_diff`](#Lib.op_set_diff)
