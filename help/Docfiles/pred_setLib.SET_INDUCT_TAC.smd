## `SET_INDUCT_TAC`

``` hol4
pred_setLib.SET_INDUCT_TAC : tactic
```

------------------------------------------------------------------------

Tactic for induction on finite sets.

`SET_INDUCT_TAC` is an induction tacic for proving properties of finite
sets. When applied to a goal of the form

``` hol4
   !s. FINITE s ==> P[s]
```

`SET_INDUCT_TAC` reduces this goal to proving that the property
`\s.P[s]` holds of the empty set and is preserved by insertion of an
element into an arbitrary finite set. Since every finite set can be
built up from the empty set `{}` by repeated insertion of values, these
subgoals imply that the property `\s.P[s]` holds of all finite sets.

The tactic specification of `SET_INDUCT_TAC` is:

``` hol4
                 A ?- !s. FINITE s ==> P
   ==========================================================  SET_INDUCT_TAC
     A |- P[{{}}/s]
     A u {FINITE s', P[s'/s], ~e IN s'} ?- P[e INSERT s'/s]
```

where `e` is a variable chosen so as not to appear free in the
assumptions `A`, and `s'` is a primed variant of `s` that does not
appear free in `A` (usually, `s'` is just `s`).

### Failure

`SET_INDUCT_TAC (A,g)` fails unless `g` has the form
`!s. FINITE s ==> P`, where the variable `s` has type `ty->bool` for
some type `ty`.
