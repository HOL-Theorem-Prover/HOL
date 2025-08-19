## `RIGHT_BETA`

``` hol4
Drule.RIGHT_BETA : (thm -> thm)
```

------------------------------------------------------------------------

Beta-reduces a top-level beta-redex on the right-hand side of an
equation.

When applied to an equational theorem, `RIGHT_BETA` applies
beta-reduction at top level to the right-hand side (only). Variables are
renamed if necessary to avoid free variable capture.

``` hol4
    A |- s = (\x. t1) t2
   ----------------------  RIGHT_BETA
     A |- s = t1[t2/x]
```

### Failure

Fails unless the theorem is equational, with its right-hand side being a
top-level beta-redex.

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV), [`Conv.BETA_RULE`](#Conv.BETA_RULE),
[`Tactic.BETA_TAC`](#Tactic.BETA_TAC),
[`Drule.RIGHT_LIST_BETA`](#Drule.RIGHT_LIST_BETA)
