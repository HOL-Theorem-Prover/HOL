## `goal_assum`

``` hol4
Tactical.goal_assum : thm_tactic -> tactic
```

------------------------------------------------------------------------

Makes the goal available as a (negated) assumption for a theorem-tactic.

An application of `goal_assum ttac` to the goal `(A,w0)` can be seen as
a tactic that first transforms the goal into `(w1::A,F)` (as if starting
a proof by contradiction, normalising `¬w0` into an equivalent `w1`);
pops the new assumption `w1` and applies the theorem-tactic `ttac` to
this theorem (`w1 ⊢ w1`); and when this completes, renormalises the
conclusion of the goal if it has turned into something of the form
`w2 ⇒ F`.

The first normalisation phase will turn something of the form `¬p` into
`p⇒F`, and will also flip outermost existential quantifiers into
universals. Thus, if the `w0` term was `∃x. P x ∧ Q (f x)`, the `w1`
term will be `∀x. P x ∧ Q (f x) ⇒ F`. The second normalisation phase
will undo this, so that if the effect of `ttac` is equivalent to a call
of `MP_TAC th'` with `th'` a universally quantified implication into
falsity, then the goal will again become an existentially quantified
conjunction.

### Failure

Fails if `ttac` fails when applied to the theorem `w1 ⊢ w1` and the goal
`(A,F)`.

### See also

[`Tactical.FIRST_ASSUM`](#Tactical.FIRST_ASSUM)
