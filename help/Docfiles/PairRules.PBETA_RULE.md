## `PBETA_RULE`

``` hol4
PairRules.PBETA_RULE : (thm -> thm)
```

------------------------------------------------------------------------

Beta-reduces all the paired beta-redexes in the conclusion of a theorem.

When applied to a theorem `A |- t`, the inference rule `PBETA_RULE`
beta-reduces all beta-redexes, at any depth, in the conclusion `t`.
Variables are renamed where necessary to avoid free variable capture.

``` hol4
    A |- ....((\p. s1) s2)....
   ----------------------------  BETA_RULE
      A |- ....(s1[s2/p])....
```

### Failure

Never fails, but will have no effect if there are no paired
beta-redexes.

### See also

[`Conv.BETA_RULE`](#Conv.BETA_RULE),
[`PairRules.PBETA_CONV`](#PairRules.PBETA_CONV),
[`PairRules.PBETA_TAC`](#PairRules.PBETA_TAC),
[`PairRules.RIGHT_PBETA`](#PairRules.RIGHT_PBETA),
[`PairRules.LEFT_PBETA`](#PairRules.LEFT_PBETA)
