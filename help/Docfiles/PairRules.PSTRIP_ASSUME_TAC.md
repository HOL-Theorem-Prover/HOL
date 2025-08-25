## `PSTRIP_ASSUME_TAC`

``` hol4
PairRules.PSTRIP_ASSUME_TAC : thm_tactic
```

------------------------------------------------------------------------

Splits a theorem into a list of theorems and then adds them to the
assumptions.

Given a theorem `th` and a goal `(A,t)`, `PSTRIP_ASSUME_TAC th` splits
`th` into a list of theorems. This is done by recursively breaking
conjunctions into separate conjuncts, cases-splitting disjunctions, and
eliminating paired existential quantifiers by choosing arbitrary
variables. Schematically, the following rules are applied:

``` hol4
           A ?- t
   ======================  PSTRIP_ASSUME_TAC (A' |- v1 /\ ... /\ vn)
    A u {v1,...,vn} ?- t

                A ?- t
   =================================  PSTRIP_ASSUME_TAC (A' |- v1 \/ ... \/ vn)
    A u {v1} ?- t ... A u {vn} ?- t

          A ?- t
   ====================  PSTRIP_ASSUME_TAC (A' |- ?p. v)
    A u {v[p'/p]} ?- t
```

where `p'` is a variant of the pair `p`.

If the conclusion of `th` is not a conjunction, a disjunction or a
paired existentially quantified term, the whole theorem `th` is added to
the assumptions.

As assumptions are generated, they are examined to see if they solve the
goal (either by being alpha-equivalent to the conclusion of the goal or
by deriving a contradiction).

The assumptions of the theorem being split are not added to the
assumptions of the goal(s), but they are recorded in the proof. This
means that if `A'` is not a subset of the assumptions `A` of the goal
(up to alpha-conversion), `PSTRIP_ASSUME_TAC (A'|-v)` results in an
invalid tactic.

### Failure

Never fails.

`PSTRIP_ASSUME_TAC` is used when applying a previously proved theorem to
solve a goal, or when enriching its assumptions so that resolution,
rewriting with assumptions and other operations involving assumptions
have more to work with.

### See also

[`PairRules.PSTRIP_THM_THEN`](#PairRules.PSTRIP_THM_THEN),
[`PairRules.PSTRIP_ASSUME_TAC`](#PairRules.PSTRIP_ASSUME_TAC),
[`PairRules.PSTRIP_GOAL_THEN`](#PairRules.PSTRIP_GOAL_THEN),
[`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC)
