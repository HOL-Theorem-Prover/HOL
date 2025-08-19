## `P_PCHOOSE_TAC`

``` hol4
PairRules.P_PCHOOSE_TAC : (term -> thm_tactic)
```

------------------------------------------------------------------------

Assumes a theorem, with existentially quantified pair replaced by a
given witness.

`P_PCHOOSE_TAC` expects a pair `q` and theorem with a paired
existentially quantified conclusion. When applied to a goal, it adds a
new assumption obtained by introducing the pair `q` as a witness for the
pair `p` whose existence is asserted in the theorem.

``` hol4
           A ?- t
   ===================  P_CHOOSE_TAC "q" (A1 |- ?p. u)
    A u {u[q/p]} ?- t         ("y" not free anywhere)
```

### Failure

Fails if the theorem's conclusion is not a paired existential
quantification, or if the first argument is not a paired structure of
variables. Failures may arise in the tactic-generating function. An
invalid tactic is produced if the introduced variable is free in `u` or
`t`, or if the theorem has any hypothesis which is not alpha-convertible
to an assumption of the goal.

### See also

[`Tactic.X_CHOOSE_TAC`](#Tactic.X_CHOOSE_TAC),
[`PairRules.PCHOOSE`](#PairRules.PCHOOSE),
[`PairRules.PCHOOSE_THEN`](#PairRules.PCHOOSE_THEN),
[`PairRules.P_PCHOOSE_THEN`](#PairRules.P_PCHOOSE_THEN)
