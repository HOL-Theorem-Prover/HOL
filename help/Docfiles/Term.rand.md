## `rand`

``` hol4
Term.rand : term -> term
```

------------------------------------------------------------------------

Returns the operand from a combination (function application).

If `M` is a combination, i.e., has the form `(t1 t2)`, then `rand M`
returns `t2`.

### Failure

Fails if `M` is not a combination.

### See also

[`Term.rator`](#Term.rator), [`Term.dest_comb`](#Term.dest_comb)
