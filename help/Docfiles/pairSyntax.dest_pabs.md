## `dest_pabs`

``` hol4
pairSyntax.dest_pabs : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a paired abstraction into abstracted pair and body.

`dest_pabs` is a term destructor for paired abstractions:
`dest_abs "\pair. t"` returns `("pair","t")`.

### Failure

Fails with `dest_pabs` if term is not a paired abstraction.

### See also

[`Term.dest_abs`](#Term.dest_abs),
[`pairSyntax.mk_pabs`](#pairSyntax.mk_pabs),
[`pairSyntax.is_pabs`](#pairSyntax.is_pabs),
[`pairSyntax.strip_pabs`](#pairSyntax.strip_pabs)
