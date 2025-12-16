## `NUM_DEPTH_CONSEQ_CONV`

``` hol4
ConseqConv.NUM_DEPTH_CONSEQ_CONV : directed_conseq_conv -> int -> directed_conseq_conv
```

------------------------------------------------------------------------

Applies a consequence conversion at most a given number of times to the
sub-terms of a term, in bottom-up order.

While `DEPTH_CONSEQ_CONV c tm` applies `c` repeatedly,
`NUM_DEPTH_CONSEQ_CONV c n tm` applies it at most n-times.

### See also

[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV),
[`ConseqConv.ONCE_DEPTH_CONSEQ_CONV`](#ConseqConv.ONCE_DEPTH_CONSEQ_CONV),
[`ConseqConv.DEPTH_CONSEQ_CONV`](#ConseqConv.DEPTH_CONSEQ_CONV),
[`ConseqConv.DEPTH_STRENGTHEN_CONSEQ_CONV`](#ConseqConv.DEPTH_STRENGTHEN_CONSEQ_CONV)
