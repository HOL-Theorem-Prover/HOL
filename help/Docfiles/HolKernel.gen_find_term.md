## `gen_find_term`

``` hol4
HolKernel.gen_find_term : (term list * term -> 'a option) -> term -> 'a option
```

------------------------------------------------------------------------

Finds first value in range of partial function mapped over sub-terms of
a term.

If a call to `gen_find_term f t` returns `SOME v`, then that result is
the first value returned by a call of function `f` to one of the
sub-terms of term `t`. The function `f` is successively passed sub-terms
of `t` starting with `t` itself and then proceeding in a top-down,
left-to-right traversal.

The additional list of terms passed to the function `f` is the list of
bound variables "governing" the sub-term in question, with the innermost
bound variable first in the list.

### Failure

A call to `gen_find_term f t` will fail if `f` fails when applied to any
of the sub-terms of `t`.

### Example

``` hol4
> gen_find_term (fn x => SOME x) ``SUC x``;
val it = SOME ([], ``SUC x``) : (term list * term) option

> gen_find_term
    (fn (bvs,t) => if null bvs andalso
                      (is_var t orelse numSyntax.is_numeral t)
                   then
                     Lib.total (match_term ``x:num``) t
                   else NONE)
    ``SUC z + (\y. y) 5``;
val it =
  SOME ([{redex = ``x``, residue = ``z``}], [])] :
   ((term, term) Term.subst * (hol_type, hol_type) Term.subst) option
```

### Comments

This function is used to implement `bvk_find_term`. This function could
itself be approximated by returning the last value in the list returned
by `gen_find_terms`. Such an implementation would be less efficient
because it would unnecessarily construct a list of all possible results.
It would also be semantically different if `f` had side effects.

### See also

[`HolKernel.bvk_find_term`](#HolKernel.bvk_find_term),
[`HolKernel.find_term`](#HolKernel.find_term),
[`HolKernel.gen_find_terms`](#HolKernel.gen_find_terms)
