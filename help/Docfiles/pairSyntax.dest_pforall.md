## `dest_pforall`

``` hol4
pairSyntax.dest_pforall : term -> term * term
```

------------------------------------------------------------------------

Breaks apart paired universal quantifiers into the bound pair and the
body.

`dest_pforall` is a term destructor for paired universal quantification.
The application of `dest_pforall` to `"!pair. t"` returns
`("pair","t")`.

### Failure

Fails with `dest_pforall` if term is not a paired universal
quantification.

### See also

[`boolSyntax.dest_forall`](#boolSyntax.dest_forall),
[`pairSyntax.is_pforall`](#pairSyntax.is_pforall),
[`pairSyntax.strip_pforall`](#pairSyntax.strip_pforall)
