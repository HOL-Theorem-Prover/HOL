## `dest_forall`

``` hol4
boolSyntax.dest_forall : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a universally quantified term into quantified variable and
body.

If `M` has the form `!x. t`, then `dest_forall M` returns `(x,t)`.

### Failure

Fails if `M` is not a universal quantification.

### See also

[`boolSyntax.mk_forall`](#boolSyntax.mk_forall),
[`boolSyntax.is_forall`](#boolSyntax.is_forall),
[`boolSyntax.strip_forall`](#boolSyntax.strip_forall),
[`boolSyntax.list_mk_forall`](#boolSyntax.list_mk_forall)
