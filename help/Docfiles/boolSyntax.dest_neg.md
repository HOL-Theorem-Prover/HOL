## `dest_neg`

``` hol4
boolSyntax.dest_neg : term -> term
```

------------------------------------------------------------------------

Breaks apart a negation, returning its body.

`dest_neg` is a term destructor for negations: if `M` has the form `~t`,
then `dest_neg M` returns `t`.

### Failure

Fails with `dest_neg` if term is not a negation.

### See also

[`boolSyntax.mk_neg`](#boolSyntax.mk_neg),
[`boolSyntax.is_neg`](#boolSyntax.is_neg)
