## `is_imp`

``` hol4
boolSyntax.is_imp : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is an implication or a negation.

If `M` has the form `t1 ==> t2`, or the form `~t`, then `is_imp M`
returns `true`. If the term is neither an implication nor a negation the
result is `false`.

### Failure

Never fails.

### Comments

Yields true of negations because `dest_imp` destructs negations (for
backwards compatibility with PPLAMBDA). Use `is_imp_only` if you don't
want this behaviour.

### See also

[`boolSyntax.mk_imp`](#boolSyntax.mk_imp),
[`boolSyntax.dest_imp`](#boolSyntax.dest_imp),
[`boolSyntax.is_imp_only`](#boolSyntax.is_imp_only),
[`boolSyntax.dest_imp_only`](#boolSyntax.dest_imp_only)
