## `body`

``` hol4
Term.body : term -> term
```

------------------------------------------------------------------------

Returns the body of an abstraction.

If `M` is a lambda abstraction, i.e, has the form `\v. t`, then `body M`
returns `t`.

### Failure

Fails unless `M` is an abstraction.

### See also

[`Term.bvar`](#Term.bvar), [`Term.dest_abs`](#Term.dest_abs)
