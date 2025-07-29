## `GEN_ALPHA_CONV`

``` hol4
Drule.GEN_ALPHA_CONV : term -> conv
```

------------------------------------------------------------------------

Renames the bound variable of an abstraction, a quantified term, or
other binder application.

The conversion `GEN_ALPHA_CONV` provides alpha conversion for lambda
abstractions of the form `\y.t`, quantified terms of the forms `!y.t`,
`?y.t` or `?!y.t`, and epsilon terms of the form `@y.t`. In general, if
`B` is a binder constant, then `GEN_ALPHA_CONV` implements alpha
conversion for applications of the form `B y.t`.

If `tm` is an abstraction `\y.t` or an application of a binder to an
abstraction `B y.t`, where the bound variable `y` has type `ty`, and if
`x` is a variable also of type `ty`, then `GEN_ALPHA_CONV x tm` returns
one of the theorems:

``` hol4
   |- (\y.t)  = (\x'. t[x'/y])
   |- (B y.t)  = (B x'. t[x'/y])
```

depending on whether the input term is `\y.t` or `B y.t` respectively.
The variable `x':ty` in the resulting theorem is a primed variant of `x`
chosen so as not to be free in the term provided as the second argument
to `GEN_ALPHA_CONV`.

### Failure

`GEN_ALPHA_CONV x tm` fails if `x` is not a variable, or if `tm` does
not have one of the forms `\y.t` or `B y.t`, where `B` is a binder.
`GEN_ALPHA_CONV x tm` also fails if `tm` does have one of these forms,
but types of the variables `x` and `y` differ.

### See also

[`Thm.ALPHA`](#Thm.ALPHA), [`Drule.ALPHA_CONV`](#Drule.ALPHA_CONV),
[`boolSyntax.new_binder_definition`](#boolSyntax.new_binder_definition)
