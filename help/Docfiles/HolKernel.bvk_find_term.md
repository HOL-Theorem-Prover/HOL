## `bvk_find_term`

``` hol4
HolKernel.bvk_find_term : (term list * term -> bool) -> (term -> 'a) -> term -> 'a option
```

------------------------------------------------------------------------

Finds a sub-term satisfying predicate argument; applies a continuation.

A call to `bvk_find_term P k tm` searches `tm` for a sub-term satisfying
`P` and calls the continuation `k` on the first that it finds. If `k`
succeeds on this sub-term, the result is wrapped in `SOME` and returned
to the caller. If `k` raises a `HOL_ERR` exception on the sub-term,
control returns to `bvk_find_term`, which continues to look for a
sub-term satisfying `P`. Other exceptions are returned to the caller. If
there is no sub-term that both satisfies `P` and on which `k` operates
successfully, the result is `NONE`.

The search order is top-down, left-to-right (i.e., rators of combs are
examined before rands).

As with `find_term`, `P` should be total. In addition, `P` is given not
just the sub-term of interest, but also the stack of bound variables
that have scope over the sub-term, with the innermost bound variables
appearing earlier in the list.

### Failure

Fails if the predicate argument fails (i.e., raises an exception;
returning false is acceptable) on a sub-term, or if the contination
argument raises a non-`HOL_ERR` exception on a sub-term on which the
predicate has returned true.

### Example

The `RED_CONV` function from `reduceLib` reduces a ground arithmetic
term over the natural numbers, failing if the term is not of the right
shape.

``` hol4
   - val find = bvk_find_term (equal ``:num`` o type_of o #2)
                              reduceLib.RED_CONV;
   > val find = fn : term -> thm option

   - find ``SUC n``;
   > val it = NONE : thm option

   - find ``2 * 3 + SUC n``;
   > val it = SOME |- 2 * 3 = 6 : thm option

   - find ``SUC n + 2 * 3``;
   > val it = SOME |- 2 * 3 = 6 : thm option

   - find ``2 + 1 + SUC n + 2 * 3``;
   > val it = SOME |- 2 + 1 = 3 : thm option
```

### See also

[`HolKernel.find_term`](#HolKernel.find_term),
[`HolKernel.find_terms`](#HolKernel.find_terms)
