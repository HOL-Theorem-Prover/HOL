## `RIGHT_LIST_PBETA`

``` hol4
PairRules.RIGHT_LIST_PBETA : (thm -> thm)
```

------------------------------------------------------------------------

Iteratively beta-reduces a top-level paired beta-redex on the right-hand
side of an equation.

When applied to an equational theorem, `RIGHT_LIST_PBETA` applies paired
beta-reduction over a top-level chain of beta-redexes to the right-hand
side (only). Variables are renamed if necessary to avoid free variable
capture.

``` hol4
    A |- s = (\p1...pn. t) q1 ... qn
   ----------------------------------  RIGHT_LIST_BETA
       A |- s = t[q1/p1]...[qn/pn]
```

### Failure

Fails unless the theorem is equational, with its right-hand side being a
top-level paired beta-redex.

### See also

[`Drule.RIGHT_LIST_BETA`](#Drule.RIGHT_LIST_BETA),
[`PairRules.PBETA_CONV`](#PairRules.PBETA_CONV),
[`PairRules.PBETA_RULE`](#PairRules.PBETA_RULE),
[`PairRules.PBETA_TAC`](#PairRules.PBETA_TAC),
[`PairRules.LIST_PBETA_CONV`](#PairRules.LIST_PBETA_CONV),
[`PairRules.RIGHT_PBETA`](#PairRules.RIGHT_PBETA),
[`PairRules.LEFT_PBETA`](#PairRules.LEFT_PBETA),
[`PairRules.LEFT_LIST_PBETA`](#PairRules.LEFT_LIST_PBETA)
