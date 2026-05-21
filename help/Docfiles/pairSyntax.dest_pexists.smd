## `dest_pexists`

``` hol4
pairSyntax.dest_pexists : term -> term * term
```

------------------------------------------------------------------------

Breaks apart paired existential quantifiers into the bound pair and the
body.

`dest_pexists` is a term destructor for paired existential
quantification. The application of `dest_pexists` to `?pair. t` returns
`(pair,t)`.

### Failure

Fails with `dest_pexists` if term is not a paired existential
quantification.

### See also

[`boolSyntax.dest_exists`](#boolSyntax.dest_exists),
[`pairSyntax.is_pexists`](#pairSyntax.is_pexists),
[`pairSyntax.strip_pexists`](#pairSyntax.strip_pexists)
