## `CONSEQ_CONV_direction`

``` hol4
ConseqConv.type CONSEQ_CONV_direction
```

------------------------------------------------------------------------

A type used to tell directed consequence conversions what the desired
result should look like.

This type is used to instruct a directed consequence conversion how to
behave. Given a direction `dir` and a boolean term `t` the result of a
directed consequence conversion `DCONSEQ_CONV` should be of the form

``` hol4
- st ==> t for dir = CONSEQ_CONV_STRENGTHEN_direction
- t ==> wt for dir = CONSEQ_CONV_WEAKEN_direction
- st ==> t, t ==> wt or t = eqt for dir = CONSEQ_CONV_UNKNOWN_direction
```

### See also

[`ConseqConv.directed_conseq_conv`](#ConseqConv.directed_conseq_conv),
[`ConseqConv.TRUE_FALSE_REFL_CONSEQ_CONV`](#ConseqConv.TRUE_FALSE_REFL_CONSEQ_CONV)
