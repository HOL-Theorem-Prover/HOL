## `dest_exists`

``` hol4
boolSyntax.dest_exists : term -> term * term
```

------------------------------------------------------------------------

Breaks apart an existentially quantified term into quantified variable
and body.

If `M` has the form `?x. t`, then `dest_exists M` returns `(x,t)`.

### Failure

Fails if `M` is not an existential quantification.

### See also

[`boolSyntax.mk_exists`](#boolSyntax.mk_exists),
[`boolSyntax.is_exists`](#boolSyntax.is_exists),
[`boolSyntax.strip_exists`](#boolSyntax.strip_exists)
