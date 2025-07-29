## `STRIP_ASSUME_TAC`

``` hol4
Tactic.STRIP_ASSUME_TAC : thm_tactic
```

------------------------------------------------------------------------

Splits a theorem into a list of theorems and then adds them to the
assumptions.

Given a theorem `th` and a goal `(A,t)`, `STRIP_ASSUME_TAC th` splits
`th` into a list of theorems. This is done by recursively breaking
conjunctions into separate conjuncts, cases-splitting disjunctions, and
eliminating existential quantifiers by choosing arbitrary variables.
Schematically, the following rules are applied:

``` hol4
           A ?- t
   ======================  STRIP_ASSUME_TAC (A' |- v1 /\ ... /\ vn)
    A u {v1,...,vn} ?- t

                A ?- t
   =================================  STRIP_ASSUME_TAC (A' |- v1 \/ ... \/ vn)
    A u {v1} ?- t ... A u {vn} ?- t

          A ?- t
   ====================  STRIP_ASSUME_TAC (A' |- ?x.v)
    A u {v[x'/x]} ?- t
```

where `x'` is a variant of `x`.

If the conclusion of `th` is not a conjunction, a disjunction or an
existentially quantified term, the whole theorem `th` is added to the
assumptions.

As assumptions are generated, they are examined to see if they solve the
goal (either by being alpha-equivalent to the conclusion of the goal or
by deriving a contradiction).

The assumptions of the theorem being split are not added to the
assumptions of the goal(s), but they are recorded in the proof. This
means that if `A'` is not a subset of the assumptions `A` of the goal
(up to alpha-conversion), `STRIP_ASSUME_TAC (A'|-v)` results in an
invalid tactic.

### Failure

Never fails.

### Example

When solving the goal

``` hol4
   ?- m = 0 + m
```

assuming the clauses for addition with `STRIP_ASSUME_TAC ADD_CLAUSES`
results in the goal

``` hol4
  {m + (SUC n) = SUC(m + n), (SUC m) + n = SUC(m + n),
   m + 0 = m, 0 + m = m, m = 0 + m} ?- m = 0 + m
```

while the same tactic directly solves the goal

``` hol4
   ?- 0 + m = m
```

`STRIP_ASSUME_TAC` is used when applying a previously proved theorem to
solve a goal, or when enriching its assumptions so that resolution,
rewriting with assumptions and other operations involving assumptions
have more to work with.

### See also

[`Tactic.ASSUME_TAC`](#Tactic.ASSUME_TAC),
[`Tactic.CHOOSE_TAC`](#Tactic.CHOOSE_TAC),
[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`Thm_cont.CONJUNCTS_THEN`](#Thm_cont.CONJUNCTS_THEN),
[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC),
[`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN)
