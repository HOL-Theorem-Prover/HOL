## `BETA_TAC`

``` hol4
Tactic.BETA_TAC : tactic
```

------------------------------------------------------------------------

Beta-reduces all the beta-redexes in the conclusion of a goal.

When applied to a goal `A ?- t`, the tactic `BETA_TAC` produces a new
goal which results from beta-reducing all beta-redexes, at any depth, in
`t`. Variables are renamed where necessary to avoid free variable
capture.

``` hol4
    A ?- ...((\x. s1) s2)...
   ==========================  BETA_TAC
     A ?- ...(s1[s2/x])...
```

### Failure

Never fails, but will have no effect if there are no beta-redexes.

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV),
[`Tactic.BETA_TAC`](#Tactic.BETA_TAC),
[`PairedLambda.PAIRED_BETA_CONV`](#PairedLambda.PAIRED_BETA_CONV)
