## `is_bool_case`

``` hol4
boolSyntax.is_bool_case : term -> bool
```

------------------------------------------------------------------------

Tests a case expression over `bool`.

If `M` has the form `bool_case M1 M2 b`, then `is_bool_case M` returns
`true`. Otherwise, it returns `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_bool_case`](#boolSyntax.mk_bool_case),
[`boolSyntax.dest_bool_case`](#boolSyntax.dest_bool_case)
