## `ETA_CONV`

``` hol4
Drule.ETA_CONV : conv
```

------------------------------------------------------------------------

Performs a toplevel eta-conversion.

`ETA_CONV` maps an eta-redex `\x. (t x)`, where `x` does not occur free
in `t`, to the theorem `|- (\x. (t x)) = t`.

### Failure

Fails if the input term is not an eta-redex.

### See also

[`Drule.RIGHT_ETA`](#Drule.RIGHT_ETA), [`Term.eta_conv`](#Term.eta_conv)
