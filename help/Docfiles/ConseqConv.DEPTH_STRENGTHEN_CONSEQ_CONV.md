## `DEPTH_STRENGTHEN_CONSEQ_CONV` {#ConseqConv.DEPTH_STRENGTHEN_CONSEQ_CONV}


```
DEPTH_STRENGTHEN_CONSEQ_CONV : conseq_conv -> conseq_conv
```



Applies a consequence conversion repeatedly to all the sub-terms of a term, in bottom-up
order.


`DEPTH_STRENGTHEN_CONSEQ_CONV c` is defined as
`DEPTH_CONSEQ_CONV (K c) CONSEQ_CONV_STRENGTHEN_direction`. So,
its just a slightly simplified interface to `DEPTH_CONSEQ_CONV`,
that tries to strengthen all the time and that does not
require the conversion to know about directions.

### See also

[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV), [`ConseqConv.ONCE_DEPTH_CONSEQ_CONV`](#ConseqConv.ONCE_DEPTH_CONSEQ_CONV), [`ConseqConv.NUM_DEPTH_CONSEQ_CONV`](#ConseqConv.NUM_DEPTH_CONSEQ_CONV), [`ConseqConv.DEPTH_CONSEQ_CONV`](#ConseqConv.DEPTH_CONSEQ_CONV)

