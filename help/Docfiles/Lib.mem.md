## `mem`

``` hol4
Lib.mem : ''a -> ''a list -> bool
```

------------------------------------------------------------------------

Tests whether a list contains a certain member.

An invocation `mem x [x1,...,xn]` returns `true` if some `xi` in the
list is equal to `x`. Otherwise it returns `false`.

### Failure

Never fails.

### Comments

Note that the type of the members of the list must be an SML equality
type. If set operations on a non-equality type are desired, use the
'op\_' variants, which take an equality predicate as an extra argument.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

### See also

[`Lib.op_mem`](#Lib.op_mem), [`Lib.insert`](#Lib.insert),
[`Lib.tryfind`](#Lib.tryfind), [`Lib.exists`](#Lib.exists),
[`Lib.all`](#Lib.all), [`Lib.assoc`](#Lib.assoc),
[`Lib.rev_assoc`](#Lib.rev_assoc)
