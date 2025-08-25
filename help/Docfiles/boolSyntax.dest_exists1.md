## `dest_exists1`

``` hol4
boolSyntax.dest_exists1 : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a unique existence term into quantified variable and body.

If `M` has the form `?!x. t`, then `dest_exists1 M` returns `(x,t)`.

### Failure

Fails if `M` is not a unique existence term.

### See also

[`boolSyntax.mk_exists1`](#boolSyntax.mk_exists1),
[`boolSyntax.is_exists1`](#boolSyntax.is_exists1)
