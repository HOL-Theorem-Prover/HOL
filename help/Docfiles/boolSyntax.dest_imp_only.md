## `dest_imp_only`

``` hol4
boolSyntax.dest_imp_only : term -> term * term
```

------------------------------------------------------------------------

Breaks an implication into antecedent and consequent.

If `M` is a term with the form `t1 ==> t2`, then `dest_imp_only M`
returns `(t1,t2)`.

### Failure

Fails if `M` is not an implication.

### See also

[`boolSyntax.mk_imp`](#boolSyntax.mk_imp),
[`boolSyntax.dest_imp`](#boolSyntax.dest_imp),
[`boolSyntax.is_imp`](#boolSyntax.is_imp),
[`boolSyntax.is_imp_only`](#boolSyntax.is_imp_only),
[`boolSyntax.strip_imp`](#boolSyntax.strip_imp),
[`boolSyntax.list_mk_imp`](#boolSyntax.list_mk_imp)
