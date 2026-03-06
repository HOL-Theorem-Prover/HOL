## `TRUE_FALSE_REFL_CONSEQ_CONV`

``` hol4
ConseqConv.TRUE_FALSE_REFL_CONSEQ_CONV : directed_conseq_conv
```

------------------------------------------------------------------------

Given a term `t` of type `bool` this directed consequence conversion
returns the theorem `|- F ==> t` for `CONSEQ_CONV_STRENGTHEN_direction`,
the theorem `|- t ==> T` for `CONSEQ_CONV_WEAKEN_direction` and
`|- t = t` for `CONSEQ_CONV_UNKNOWN_direction`.

### See also

[`ConseqConv.TRUE_CONSEQ_CONV`](#ConseqConv.TRUE_CONSEQ_CONV),
[`ConseqConv.FALSE_CONSEQ_CONV`](#ConseqConv.FALSE_CONSEQ_CONV),
[`ConseqConv.REFL_CONSEQ_CONV`](#ConseqConv.REFL_CONSEQ_CONV)
