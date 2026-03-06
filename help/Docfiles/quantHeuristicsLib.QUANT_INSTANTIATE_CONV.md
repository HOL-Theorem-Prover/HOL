## `QUANT_INSTANTIATE_CONV`

``` hol4
quantHeuristicsLib.QUANT_INSTANTIATE_CONV : quant_param list -> conv
```

------------------------------------------------------------------------

Instantiate quantifiers in a term using a given list of quantifier
heuristic parameters.

This conversion tries to instantiate quantifiers. Therefore, it uses the
given list of quantifier heuristic parameters. If the list is empty, it
knows about the usual Boolean Connectives, quantifiers and equations.
The parameter `quantHeuristicsArgsLib.std_qp` adds knowledge about
option-types, pairs, lists, records and natural numbers. The stateful
parameter `quantHeuristicsArgsLib.Type_Base_qp` can be used to extract
information about user defined datatypes.

### Example

``` hol4
> QUANT_INSTANTIATE_CONV [] ``?x. ((x=7) \/ (7 = x)) /\ P x``;
val it = |- (?x. ((x=7) \/ (7 = x)) /\ P x) = P 7 : thm

> QUANT_INSTANTIATE_CONV [] ``?x. !y. (x=7) /\ P x y``;
val it = |- (?x. !y. (x=7) /\ P x y) = (!y. P 7 y) : thm


> QUANT_INSTANTIATE_CONV [] ``?x. (f(8 + 2) = f(x + 2)) /\ P(f (x + 2))``;
val it = |- (?x. (f(8 + 2) = f(x + 2)) /\ P(f (x + 2))) = P(f (8 + 2)) : thm

> QUANT_INSTANTIATE_CONV [std_qp] ``!x. IS_SOME x ==> P x``;
val it = |- (!x. IS_SOME x ==> P x) = (!x_x'. P (SOME x_x')) : thm

> QUANT_INSTANTIATE_CONV [std_qp] ``!l. (~(l = []) ==> (LENGTH l > 0))``;
val it |- (!l. (~(l = []) ==> (LENGTH l > 0))) <=>
          (!l_t l_h. LENGTH (l_h::l_t) > 0) : thm
```

### See also

[`quantHeuristicsLib.QUANT_INST_ss`](#quantHeuristicsLib.QUANT_INST_ss),
[`quantHeuristicsLib.QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.QUANT_INSTANTIATE_TAC),
[`quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC),
[`quantHeuristicsLib.FAST_QUANT_INSTANTIATE_CONV`](#quantHeuristicsLib.FAST_QUANT_INSTANTIATE_CONV),
[`quantHeuristicsLib.FAST_QUANT_INST_ss`](#quantHeuristicsLib.FAST_QUANT_INST_ss),
[`quantHeuristicsLib.FAST_QUANT_INSTANTIATE_TAC`](#quantHeuristicsLib.FAST_QUANT_INSTANTIATE_TAC)
