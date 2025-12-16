## `FAST_ASM_QUANT_INSTANTIATE_TAC`

``` hol4
quantHeuristicsLib.FAST_ASM_QUANT_INSTANTIATE_TAC : quant_param list -> tactic
```

------------------------------------------------------------------------

A fast version of `quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC`. It
does not preprocess the term in order to minimise the number of variable
occurrences.

### See also

[`quantHeuristicsLib.QUANT_INSTANTIATE_CONV`](#quantHeuristicsLib.QUANT_INSTANTIATE_CONV),
[`quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC)
