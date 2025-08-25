## `FREEZE_THEN`

``` hol4
Tactic.FREEZE_THEN : thm_tactical
```

------------------------------------------------------------------------

'Freezes' a theorem to prevent instantiation of its free variables.

`FREEZE_THEN` expects a tactic-generating function `f:thm->tactic` and a
theorem `(A1 |- w)` as arguments. The tactic-generating function `f` is
applied to the theorem `(w |- w)`. If this tactic generates the subgoal:

``` hol4
    A0 ?- t
   =========  f (w |- w)
     A ?- t1
```

then applying `FREEZE_THEN f (A1 |- w)` to the goal `(A0 ?- t)` produces
the subgoal:

``` hol4
             A0 ?- t
   ===================  FREEZE_THEN f (A1 |- w)
    A - {w}, A1 ?- t1
```

Since the term `w` is a hypothesis of the argument to the function `f`,
none of the free variables present in `w` may be instantiated or
generalized. The hypothesis is discharged by `PROVE_HYP` upon the
completion of the proof of the subgoal.

### Failure

Failures may arise from the tactic-generating function. An invalid
tactic arises if the hypotheses of the theorem are not alpha-convertible
to assumptions of the goal.

### Example

Given the goal ``` ([ ``b < c``, ``a < b`` ], ``SUC a <= c``) ```, and
the specialized variant of the theorem `LESS_TRANS`:

``` hol4
   th = |- !p. a < b /\ b < p ==> a < p
```

`IMP_RES_TAC th` will generate several unneeded assumptions:

``` hol4
   {b < c, a < b, a < c, !p. c < p ==> b < p, !a'. a' < a ==> a' < b}
       ?- SUC a <= c
```

which can be avoided by first 'freezing' the theorem, using the tactic

``` hol4
   FREEZE_THEN IMP_RES_TAC th
```

This prevents the variables `a` and `b` from being instantiated.

``` hol4
   {b < c, a < b, a < c} ?- SUC a <= c
```

Used in serious proof hacking to limit the matches achievable by
resolution and rewriting.

### See also

[`Thm.ASSUME`](#Thm.ASSUME),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Drule.PROVE_HYP`](#Drule.PROVE_HYP),
[`Tactic.RES_TAC`](#Tactic.RES_TAC), [`Conv.REWR_CONV`](#Conv.REWR_CONV)
