## `mk_abs`

``` hol4
Term.mk_abs : term * term -> term
```

------------------------------------------------------------------------

Constructs an abstraction.

`mk_abs (v, t)` returns the lambda abstraction `\v. t`. All free
occurrences of `v` in `t` thereby become bound.

### Failure

Fails if `v` is not a variable.

### See also

[`Term.dest_abs`](#Term.dest_abs), [`Term.is_abs`](#Term.is_abs),
[`boolSyntax.list_mk_abs`](#boolSyntax.list_mk_abs),
[`Term.mk_var`](#Term.mk_var), [`Term.mk_const`](#Term.mk_const),
[`Term.mk_comb`](#Term.mk_comb)
