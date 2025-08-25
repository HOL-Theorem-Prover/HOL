## `ASM_QUANT_INSTANTIATE_TAC`

``` hol4
quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC : quant_param list -> tactic
```

------------------------------------------------------------------------

A tactic to instantiate quantifiers in a term using a given list of
quantifier heuristic parameters.

This tactic is based on `quantHeuristicsLib.QUANT_INSTANTIATE_CONV`. It
tries to instantiate quantifiers. Free variables of the goal are seen as
universally quantified by this tactic. Therefore, it tries to
instantiate these free variables.

In contrast to `quantHeuristicsLib.QUANT_INSTANTIATE_TAC` this tactic
takes the assumptions of the goal into account.

### See also

[`quantHeuristicsLib.QUANT_INSTANTIATE_CONV`](#quantHeuristicsLib.QUANT_INSTANTIATE_CONV),
[`quantHeuristicsLib.QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.QUANT_INSTANTIATE_TAC)
