## `ASM_QI_TAC`

``` hol4
bossLib.ASM_QI_TAC : tactic
```

------------------------------------------------------------------------

Try to instantiate quantifiers with some default heuristics using also
the assumptions..

`ASM_QI_TAC` is short for `ASM_QUANT_INSTANTIATE_TAC [std_qp]`.

### See also

[`bossLib.QI_TAC`](#bossLib.QI_TAC),
[`quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC),
[`quantHeuristicsLib.QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.QUANT_INSTANTIATE_TAC)
