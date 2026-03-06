## `mk_neg`

``` hol4
boolSyntax.mk_neg : (term -> term)
```

------------------------------------------------------------------------

Constructs a negation.

`mk_neg "t"` returns `"~t"`.

### Failure

Fails with `mk_neg` unless `t` is of type `bool`.

### See also

[`boolSyntax.dest_neg`](#boolSyntax.dest_neg),
[`boolSyntax.is_neg`](#boolSyntax.is_neg)
