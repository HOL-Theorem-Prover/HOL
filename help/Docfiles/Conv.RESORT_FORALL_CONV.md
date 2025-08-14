## `RESORT_FORALL_CONV`

``` hol4
Conv.RESORT_FORALL_CONV : (term list -> term list) -> conv
```

------------------------------------------------------------------------

Reorders bound variables under universal quantifiers.

A call to `RESORT_FORALL_CONV f t` strips the outer
universally-quantified variables of `t`, giving a list `vs`, such that
`t` is of the form `!vs. body`. The list `vs` is then passed to the
function argument `f`. The result of the call `f vs` is expected to be a
new list of variables `vs'`, and the result of the conversion is the
theorem

``` hol4
   |- (!vs. body) <=> (!vs'. body)
```

The function `f` is generally expected to return a permutation of the
variables appearing in the term `vs`, but may in fact introduce fresh
variables that are fresh for `body`, and may also remove variables from
`vs` that also don't appear in `body`.

### Failure

Given a term `t`, fails if `t` is not of boolean type. Fails if when
applied to the outermost universally quantified variables (permitted to
be the empty list) the function `f` returns a list of terms that are not
all variables. Also fails if either `f` returns a list that does not
include variables from `vs` that appear in the body of `t`, or if it
includes variables that are in the body, but which were not originally
bound.

### See also

[`Conv.RESORT_EXISTS_CONV`](#Conv.RESORT_EXISTS_CONV),
[`HolKernel.sort_vars`](#HolKernel.sort_vars)
