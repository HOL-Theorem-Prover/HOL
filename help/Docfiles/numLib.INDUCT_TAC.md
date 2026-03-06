## `INDUCT_TAC`

``` hol4
numLib.INDUCT_TAC : tactic
```

------------------------------------------------------------------------

Performs tactical proof by mathematical induction on the natural
numbers.

`INDUCT_TAC` reduces a goal `!n.P[n]`, where `n` has type `num`, to two
subgoals corresponding to the base and step cases in a proof by
mathematical induction on `n`. The induction hypothesis appears among
the assumptions of the subgoal for the step case. The specification of
`INDUCT_TAC` is:

``` hol4
                A ?- !n. P
    ========================================  INDUCT_TAC
     A ?- P[0/n]     A u {P} ?- P[SUC n'/n]
```

where `n'` is a primed variant of `n` that does not appear free in the
assumptions `A` (usually, `n'` just equals `n`). When `INDUCT_TAC` is
applied to a goal of the form `!n.P`, where `n` does not appear free in
`P`, the subgoals are just `A ?- P` and `A u {P} ?- P`.

### Failure

`INDUCT_TAC g` fails unless the conclusion of the goal `g` has the form
`!n.t`, where the variable `n` has type `num`.
