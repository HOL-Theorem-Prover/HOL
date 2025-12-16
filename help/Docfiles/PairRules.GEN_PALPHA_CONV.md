## `GEN_PALPHA_CONV`

``` hol4
PairRules.GEN_PALPHA_CONV : term -> conv
```

------------------------------------------------------------------------

Renames the bound pair of a paired abstraction, quantified term, or
other binder.

The conversion `GEN_PALPHA_CONV` provides alpha conversion for lambda
abstractions of the form `\p.t`, quantified terms of the forms `!p.t`,
`?p.t` or `?!p.t`, and epsilon terms of the form `@p.t`.

The renaming of pairs is as described for `PALPHA_CONV`.

### Failure

`GEN_PALPHA_CONV q tm` fails if `q` is not a variable, or if `tm` does
not have one of the required forms. `GEN_ALPHA_CONV q tm` also fails if
`tm` does have one of these forms, but types of the variables `p` and
`q` differ.

### See also

[`Drule.GEN_ALPHA_CONV`](#Drule.GEN_ALPHA_CONV),
[`PairRules.PALPHA`](#PairRules.PALPHA),
[`PairRules.PALPHA_CONV`](#PairRules.PALPHA_CONV)
