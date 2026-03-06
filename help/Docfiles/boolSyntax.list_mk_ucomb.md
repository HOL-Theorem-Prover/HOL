## `list_mk_ucomb`

``` hol4
boolSyntax.list_mk_ucomb : term * term list -> term
```

------------------------------------------------------------------------

Folds `mk_ucomb` over a series of arguments.

A call to `list_mk_ucomb(f, args)` combines `f` with each of the
elements of the list `args` in turn, moving from left to right. If
`args` is empty, then the result is simply `f`. When `args` is
non-empty, the growing application-term is created with successive calls
to `mk_ucomb`, possibly causing type variables in any of the terms to
become instantiated.

### Failure

Fails if any of the underlying calls to `mk_ucomb` fails, which will
occur if the type of the accumulating term (starting with `f`) is not of
a function type, or if it has a domain type that can not be instantiated
to equal the type of some instantiation of the next argument term.

### Comments

`list_mk_ucomb` is to `mk_ucomb` what `list_mk_comb` is to `mk_comb`.

### See also

[`Term.list_mk_comb`](#Term.list_mk_comb),
[`Term.mk_comb`](#Term.mk_comb),
[`boolSyntax.mk_ucomb`](#boolSyntax.mk_ucomb)
