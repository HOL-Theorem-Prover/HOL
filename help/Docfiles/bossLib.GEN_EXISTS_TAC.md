## `GEN_EXISTS_TAC`

``` hol4
bossLib.GEN_EXISTS_TAC : string -> Parse.term Lib.frag list -> tactic
```

------------------------------------------------------------------------

Instantiate a quantifier at subposition.

`GEN_EXISTS_TAC v_name i` tries to instantiate a quantifier for a
variable with name `v_name` with `i`. It is short for
`quantHeuristicsLib.QUANT_TAC [(v, i, [])]`. It can be seen as a
generalisation of `Q.EXISTS_TAC`.

### See also

[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC),
[`quantHeuristicsLib.QUANT_TAC`](#quantHeuristicsLib.QUANT_TAC)
