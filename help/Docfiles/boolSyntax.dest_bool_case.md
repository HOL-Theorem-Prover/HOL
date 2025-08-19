## `dest_bool_case`

``` hol4
boolSyntax.dest_bool_case : term -> term * term * term
```

------------------------------------------------------------------------

Destructs a case expression over `bool`.

If `M` has the form `bool_case M1 M2 b`, then `dest_bool_case M` returns
`M1,M2,b`.

### Failure

Fails if `M` is not a full application of the `bool_case` constant.

### See also

[`boolSyntax.mk_bool_case`](#boolSyntax.mk_bool_case),
[`boolSyntax.is_bool_case`](#boolSyntax.is_bool_case)
