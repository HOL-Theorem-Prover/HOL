## `bvar`

``` hol4
Term.bvar : term -> term
```

------------------------------------------------------------------------

Returns the bound variable of an abstraction.

If `M` is a lambda abstraction, i.e, has the form `\v. t`, then `bvar M`
returns `v`.

### Failure

Fails unless `M` is an abstraction.

### See also

[`Term.body`](#Term.body), [`Term.dest_abs`](#Term.dest_abs)
