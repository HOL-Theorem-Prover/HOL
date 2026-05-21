## `PBETA_TAC`

``` hol4
PairRules.PBETA_TAC : tactic
```

------------------------------------------------------------------------

Beta-reduces all the paired beta-redexes in the conclusion of a goal.

When applied to a goal `A ?- t`, the tactic `PBETA_TAC` produces a new
goal which results from beta-reducing all paired beta-redexes, at any
depth, in `t`. Variables are renamed where necessary to avoid free
variable capture.

``` hol4
    A ?- ...((\p. s1) s2)...
   ==========================  PBETA_TAC
     A ?- ...(s1[s2/p])...
```

### Failure

Never fails, but will have no effect if there are no paired
beta-redexes.

### See also

[`Tactic.BETA_TAC`](#Tactic.BETA_TAC),
[`PairRules.PBETA_CONV`](#PairRules.PBETA_CONV),
[`PairRules.PBETA_RULE`](#PairRules.PBETA_RULE)
