## `PSELECT_ELIM`

``` hol4
PairRules.PSELECT_ELIM : thm -> term * thm -> thm
```

------------------------------------------------------------------------

Eliminates a paired epsilon term, using deduction from a particular
instance.

`PSELECT_ELIM` expects two arguments, a theorem `th1`, and a pair
`(p,th2): term * thm`. The conclusion of `th1` must have the form
`P($@ P)`, which asserts that the epsilon term `$@ P` denotes some value
at which `P` holds. The paired variable structure `p` appears only in
the assumption `P p` of the theorem `th2`. The conclusion of the
resulting theorem matches that of `th2`, and the hypotheses include the
union of all hypotheses of the premises excepting `P p`.

``` hol4
    A1 |- P($@ P)     A2 u {P p} |- t
   -------------------------------------  PSELECT_ELIM th1 (p ,th2)
              A1 u A2 |- t
```

where `p` is not free in `A2`. If `p` appears in the conclusion of
`th2`, the epsilon term will NOT be eliminated, and the conclusion will
be `t[$@ P/p]`.

### Failure

Fails if the first theorem is not of the form `A1 |- P($@ P)`, or if any
of the variables from the variable structure `p` occur free in any other
assumption of `th2`.

### See also

[`Drule.SELECT_ELIM`](#Drule.SELECT_ELIM),
[`PairRules.PCHOOSE`](#PairRules.PCHOOSE),
[`PairRules.PSELECT_CONV`](#PairRules.PSELECT_CONV),
[`PairRules.PSELECT_INTRO`](#PairRules.PSELECT_INTRO),
[`PairRules.PSELECT_RULE`](#PairRules.PSELECT_RULE)
