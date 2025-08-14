## `mk_imp`

``` hol4
boolSyntax.mk_imp : term * term -> term
```

------------------------------------------------------------------------

Constructs an implication.

If `t1` and `t2` are terms of type `bool`, then `mk_imp(t1,t2)`
constructs the term `t1 ==> t2`.

### Failure

Fails if `t1` and `t2` are not both of type `bool`.

### See also

[`boolSyntax.dest_imp`](#boolSyntax.dest_imp),
[`boolSyntax.dest_imp_only`](#boolSyntax.dest_imp_only),
[`boolSyntax.is_imp`](#boolSyntax.is_imp),
[`boolSyntax.is_imp_only`](#boolSyntax.is_imp_only),
[`boolSyntax.list_mk_imp`](#boolSyntax.list_mk_imp)
