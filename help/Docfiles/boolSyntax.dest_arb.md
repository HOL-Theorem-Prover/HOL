## `dest_arb`

``` hol4
boolSyntax.dest_arb : term -> hol_type
```

------------------------------------------------------------------------

Extract the type of an instance of the `ARB` constant.

If `M` is an instance of the constant `ARB` with type `ty`, then
`dest_arb M` equals `ty`.

### Failure

Fails if `M` is not an instance of `ARB`.

### Comments

When it succeeds, an invocation of `dest_arb` is equivalent to
`type_of`.

### See also

[`boolSyntax.mk_arb`](#boolSyntax.mk_arb),
[`boolSyntax.is_arb`](#boolSyntax.is_arb)
