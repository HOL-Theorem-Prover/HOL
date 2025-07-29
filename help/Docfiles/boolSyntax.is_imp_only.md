## `is_imp_only`

``` hol4
boolSyntax.is_imp_only : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is an implication.

If `M` has the form `t1 ==> t2` then `is_imp_only M` returns `true`. If
the term is not an implication, the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.is_imp`](#boolSyntax.is_imp),
[`boolSyntax.mk_imp`](#boolSyntax.mk_imp),
[`boolSyntax.dest_imp`](#boolSyntax.dest_imp),
[`boolSyntax.dest_imp_only`](#boolSyntax.dest_imp_only),
[`boolSyntax.list_mk_imp`](#boolSyntax.list_mk_imp),
[`boolSyntax.strip_imp`](#boolSyntax.strip_imp)
