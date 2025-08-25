## `find_term`

``` hol4
HolKernel.find_term : (term -> bool) -> term -> term
```

------------------------------------------------------------------------

Finds a sub-term satisfying a predicate.

A call to `find_term P t` returns a sub-term of `t` that satisfies the
predicate `P` if there is one. Otherwise it raises a `HOL_ERR`
exception. The search is done in a top-down, left-to-right order (i.e.,
rators of combs are examined before rands).

### Failure

Fails if the predicate fails when applied to any of the sub-terms of the
term argument. Also fails if there is no sub-term satisfying the
predicate.

### Example

``` hol4
- find_term Literal.is_numeral ``2 + x + 3``;
> val it = ``2`` : term

- find_term Literal.is_numeral ``x + y``;
Exception HOL_ERR {...}
```

### See also

[`HolKernel.bvk_find_term`](#HolKernel.bvk_find_term),
[`HolKernel.find_terms`](#HolKernel.find_terms)
