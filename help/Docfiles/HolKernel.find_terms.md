## `find_terms`

``` hol4
HolKernel.find_terms : (term -> bool) -> term -> term list
```

------------------------------------------------------------------------

Traverses a term, returning a list of sub-terms satisfying a predicate.

A call to `find_terms P t` returns a list of sub-terms of `t` that
satisfy `P`. The resulting list is ordered as if the traversal had been
bottom-up and right-to-left (i.e., the rands of combs visited before
their rators). The term `t` is itself considered a possible sub-term of
`t`.

### Failure

Only fails if the predicate fails on one of the term's sub-terms.

### Example

``` hol4
- find_terms (fn _ => true) ``x + y``;
> val it = [``y``, ``x``, ``$+``, ``$+ x``, ``x + y``]

- find_terms Literal.is_numeral ``x + y``;
> val it = [] : term list

- find_terms Literal.is_numeral ``1 + x + 2 + y``;
> val it = [``2``, ``1``] : term list
```

### See also

[`HolKernel.bvk_find_term`](#HolKernel.bvk_find_term),
[`HolKernel.find_term`](#HolKernel.find_term)
