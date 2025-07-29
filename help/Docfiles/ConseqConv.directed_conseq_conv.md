## `directed_conseq_conv`

``` hol4
ConseqConv.type directed_conseq_conv
```

------------------------------------------------------------------------

A type for consequence conversions that can be instructed on whether to
strengthen or weaken a given term.

Given a `CONSEQ_CONV_direction`, a directed consequence conversion tries
to strengthen, weaken or whatever it can depending on the given
direction.

### See also

[`ConseqConv.conseq_conv`](#ConseqConv.conseq_conv),
[`ConseqConv.CONSEQ_CONV_direction`](#ConseqConv.CONSEQ_CONV_direction)
