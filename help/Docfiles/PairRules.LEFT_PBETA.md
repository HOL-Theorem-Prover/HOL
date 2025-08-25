## `LEFT_PBETA`

``` hol4
PairRules.LEFT_PBETA : (thm -> thm)
```

------------------------------------------------------------------------

Beta-reduces a top-level paired beta-redex on the left-hand side of an
equation.

When applied to an equational theorem, `LEFT_PBETA` applies paired
beta-reduction at top level to the left-hand side (only). Variables are
renamed if necessary to avoid free variable capture.

``` hol4
    A |- (\x. t1) t2 = s
   ----------------------  LEFT_PBETA
     A |- t1[t2/x] = s
```

### Failure

Fails unless the theorem is equational, with its left-hand side being a
top-level paired beta-redex.

### See also

[`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA),
[`PairRules.PBETA_CONV`](#PairRules.PBETA_CONV),
[`PairRules.PBETA_RULE`](#PairRules.PBETA_RULE),
[`PairRules.PBETA_TAC`](#PairRules.PBETA_TAC),
[`PairRules.RIGHT_PBETA`](#PairRules.RIGHT_PBETA),
[`PairRules.RIGHT_LIST_PBETA`](#PairRules.RIGHT_LIST_PBETA),
[`PairRules.LEFT_LIST_PBETA`](#PairRules.LEFT_LIST_PBETA)
