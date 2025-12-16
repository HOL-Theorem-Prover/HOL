## `namedCases_on`

``` hol4
bossLib.namedCases_on : term quotation -> string list -> tactic
```

------------------------------------------------------------------------

Case split on type of given term, using given names for introduced
constructor arguments.

An application of `namedCases_on q [s1, ..., sn]` to a goal `A ?- P`
first parses `q` in the context of the goal to yield a term `tm:ty`,
then uses `ty` to look up a a so-called "nchotomy" theorem installed in
the system database of declared datatypes, then performs a case split on
how `tm` can be constructed. The strings `s1, ..., sn` designate the
names to be used as arguments of the constructor in each case. This
yields the goals

``` hol4
    (A, tm = <constr>1 <names>1 ?- P)
     ,...,
    (A, tm = <constr>n <names>n ?- P)
```

For a datatype with `n` constructors, `n` strings are expected to be
supplied. If no strings are supplied, the system will use a default
naming scheme. If the `i`th constructor has no arguments, then `si`
should be the empty string. If the `i`th constructor has `k` arguments,
then `si` should consist of `k` space-separated names. In case a name
does not need to be specified, an underscore `_` or dash `-` can be
supplied, in which case a default name will be conjured up.

In case `ty` is a product type `ty1 # ... # tyi`, `namedCases_on q [s]`
will iteratively case split on all product types in `ty`, thus replacing
`x:ty` by a tuple with `i` variables, the names of which are taken from
`s`.

### Failure

Fails if there is not an nchotomy theorem installed for the topmost type
constructor of `ty`. If `slist` is not the empty list,
`namedCases_on q slist` will fail if the length of `slist` is not equal
to the number of constructors in the nchotomy theorem. Fails if the
given names for arguments of an introduced constructor are not
equinumerous with the arguments.

### Comments

This is a version of `namedCases` where the (free) term being split on
is specified.

### See also

[`bossLib.namedCases`](#bossLib.namedCases),
[`bossLib.Cases_on`](#bossLib.Cases_on),
[`bossLib.Cases`](#bossLib.Cases),
[`TypeBase.nchotomy_of`](#TypeBase.nchotomy_of)
