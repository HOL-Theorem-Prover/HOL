## `genvars`

``` hol4
Term.genvars : hol_type -> int -> term list
```

------------------------------------------------------------------------

Generate a specified number of fresh variables.

An invocation `genvars ty n` will invoke `genvar` `n` times and return
the resulting list of variables.

### Failure

Never fails. If `n` is less-than-or-equal to zero, the empty list is
returned.

### Example

``` hol4
- genvars alpha 3;
> val it = [`%%genvar%%1558`, `%%genvar%%1559`, `%%genvar%%1560`] : term list
```

### See also

[`Term.genvar`](#Term.genvar), [`Term.mk_var`](#Term.mk_var)
