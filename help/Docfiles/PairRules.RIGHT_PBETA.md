## `RIGHT_PBETA`

``` hol4
PairRules.RIGHT_PBETA : (thm -> thm)
```

------------------------------------------------------------------------

Beta-reduces a top-level paired beta-redex on the right-hand side of an
equation.

When applied to an equational theorem, `RIGHT_PBETA` applies paired
beta-reduction at top level to the right-hand side (only). Variables are
renamed if necessary to avoid free variable capture.

``` hol4
    A |- s = (\p. t1) t2
   ----------------------  RIGHT_PBETA
     A |- s = t1[t2/p]
```

### Failure

Fails unless the theorem is equational, with its right-hand side being a
top-level paired beta-redex.

### See also

[`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA),
[`PairRules.PBETA_CONV`](#PairRules.PBETA_CONV),
[`PairRules.PBETA_RULE`](#PairRules.PBETA_RULE),
[`PairRules.PBETA_TAC`](#PairRules.PBETA_TAC),
[`PairRules.RIGHT_LIST_PBETA`](#PairRules.RIGHT_LIST_PBETA),
[`PairRules.LEFT_PBETA`](#PairRules.LEFT_PBETA),
[`PairRules.LEFT_LIST_PBETA`](#PairRules.LEFT_LIST_PBETA)
