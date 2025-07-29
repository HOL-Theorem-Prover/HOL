## `rator`

``` hol4
Term.rator : term -> term
```

------------------------------------------------------------------------

Returns the operator from a combination (function application).

If `M` is a combination, i.e., has the form `(t1 t2)`, then `rator M`
returns `t1`.

### Failure

Fails if `M` is not a combination.

### See also

[`Term.rand`](#Term.rand), [`Term.dest_comb`](#Term.dest_comb)
