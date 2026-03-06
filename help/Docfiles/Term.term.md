## `term`

``` hol4
Term.eqtype term
```

------------------------------------------------------------------------

ML datatype of HOL terms.

The ML abstract type `term` represents the set of HOL terms, which is
essentially the simply typed lambda calculus of Church. A term may be a
variable, a constant, an application of one term to another, or a lambda
abstraction.

### Comments

Since `term` is an ML eqtype, any two `term`s `tm1` and `tm2` can be
tested for equality by `tm1 = tm2`. However, the fundamental notion of
equality for terms is implemented by `aconv`.

Since term is an abstract type, access to its representation is mediated
by the interface presented by the `Term` structure.

### See also

[`Type.hol_type`](#Type.hol_type)
