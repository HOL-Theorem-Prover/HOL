## `PCHOOSE_TAC`

``` hol4
PairRules.PCHOOSE_TAC : thm_tactic
```

------------------------------------------------------------------------

Adds the body of a paired existentially quantified theorem to the
assumptions of a goal.

When applied to a theorem `A' |- ?p. t` and a goal, `CHOOSE_TAC` adds
`t[p'/p]` to the assumptions of the goal, where `p'` is a variant of the
pair `p` which has no components free in the assumption list; normally
`p'` is just `p`.

``` hol4
         A ?- u
   ====================  CHOOSE_TAC (A' |- ?q. t)
    A u {t[p'/p]} ?- u
```

Unless `A'` is a subset of `A`, this is not a valid tactic.

### Failure

Fails unless the given theorem is a paired existential quantification.

### See also

[`Tactic.CHOOSE_TAC`](#Tactic.CHOOSE_TAC),
[`PairRules.PCHOOSE_THEN`](#PairRules.PCHOOSE_THEN),
[`PairRules.P_PCHOOSE_TAC`](#PairRules.P_PCHOOSE_TAC)
