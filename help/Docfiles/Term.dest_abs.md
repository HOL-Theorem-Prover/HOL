## `dest_abs`

``` hol4
Term.dest_abs : term -> term * term
```

------------------------------------------------------------------------

Breaks apart an abstraction into abstracted variable and body.

`dest_abs` is a term destructor for abstractions: if `M` is a term of
the form `\v.t`, then `dest_abs M` returns `(v,t)`.

### Failure

Fails if it is not given a lambda abstraction.

### See also

[`Term.mk_abs`](#Term.mk_abs), [`Term.is_abs`](#Term.is_abs),
[`Term.dest_var`](#Term.dest_var),
[`Term.dest_const`](#Term.dest_const),
[`Term.dest_comb`](#Term.dest_comb),
[`boolSyntax.strip_abs`](#boolSyntax.strip_abs)
