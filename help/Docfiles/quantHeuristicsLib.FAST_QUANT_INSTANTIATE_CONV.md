## `FAST_QUANT_INSTANTIATE_CONV`

``` hol4
quantHeuristicsLib.FAST_QUANT_INSTANTIATE_CONV : quant_param list -> conv
```

------------------------------------------------------------------------

A fast version of `quantHeuristicsLib.QUANT_INSTANTIATE_CONV`. It does
not preprocess the term in order to minimise the number of variable
occurrences.

### See also

[`quantHeuristicsLib.QUANT_INSTANTIATE_CONV`](#quantHeuristicsLib.QUANT_INSTANTIATE_CONV),
[`quantHeuristicsLib.FAST_QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.FAST_QUANT_INSTANTIATE_TAC)
