## `ALPHA_CONV`

``` hol4
Drule.ALPHA_CONV : term -> conv
```

------------------------------------------------------------------------

Renames the bound variable of a lambda-abstraction.

If `x` is a variable of type `ty` and `M` is an abstraction (with bound
variable `y` of type `ty` and body `t`), then `ALPHA_CONV x M` returns
the theorem:

``` hol4
   |- (\y.t) = (\x'. t[x'/y])
```

where the variable `x':ty` is a primed variant of `x` chosen so as not
to be free in `\y.t`.

### Failure

`ALPHA_CONV x tm` fails if `x` is not a variable, if `tm` is not an
abstraction, or if `x` is a variable `v` and `tm` is a lambda
abstraction `\y.t` but the types of `v` and `y` differ.

### See also

[`Thm.ALPHA`](#Thm.ALPHA),
[`Drule.GEN_ALPHA_CONV`](#Drule.GEN_ALPHA_CONV)
