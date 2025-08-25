## `LIST_INDUCT_TAC`

``` hol4
listLib.LIST_INDUCT_TAC : tactic
```

------------------------------------------------------------------------

Performs tactical proof by structural induction on lists.

`LIST_INDUCT_TAC` reduces a goal `!l.P[l]`, where `l` ranges over lists,
to two subgoals corresponding to the base and step cases in a proof by
structural induction on `l`. The induction hypothesis appears among the
assumptions of the subgoal for the step case. The specification of
`LIST_INDUCT_TAC` is:

``` hol4
                     A ?- !l. P
   =====================================================  LIST_INDUCT_TAC
    A |- P[NIL/l]   A u {{P[l'/l]}} ?- !h. P[CONS h l'/l]
```

where `l'` is a primed variant of `l` that does not appear free in the
assumptions `A` (usually, `l'` is just `l`). When `LIST_INDUCT_TAC` is
applied to a goal of the form `!l.P`, where `l` does not appear free in
`P`, the subgoals are just `A ?- P` and `A u {{P}} ?- !h.P`.

### Failure

`LIST_INDUCT_TAC g` fails unless the conclusion of the goal `g` has the
form `!l.t`, where the variable `l` has type `(ty)list` for some type
`ty`.

### See also

[`listLib.EQ_LENGTH_INDUCT_TAC`](#listLib.EQ_LENGTH_INDUCT_TAC),
[`listLib.EQ_LENGTH_SNOC_INDUCT_TAC`](#listLib.EQ_LENGTH_SNOC_INDUCT_TAC),
[`listLib.SNOC_INDUCT_TAC`](#listLib.SNOC_INDUCT_TAC)
