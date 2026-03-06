## `irule`

``` hol4
Tactic.irule : thm_tactic
```

------------------------------------------------------------------------

Reduces the goal using a supplied implication, with matching.

When applied to a theorem of the form

``` hol4
   A' |- !x1...xn. s ==> !y1...ym. t ==> !z1...zk. u
```

`irule` produces a tactic that reduces a goal whose conclusion `u'` is a
substitution and/or type instance of `u` to the corresponding instances
of `s` and of `t`. Any variables free in `s` or `t` but not in `u` will
be existentially quantified in the resulting subgoal, and a variable
free in both `s` and `t` will result in a subgoal which is `s /\ t`,
existentially quantified

The following diagram is simplified: more implications and quantified
variables than shown are allowed.

``` hol4
     A ?- u'
  =========================  irule (A' |- !x. s ==> !y. t ==> u)
   A ?- (?z. s') /\ ?w. t'
```

where `z` and `w` are (type instances of) variables among `x`, `y` that
do not occur free in `s`, `t`. The assumptions `A'`, instantiated, are
added as further new subgoals.

### Failure

Fails unless the theorem, when stripped of universal quantification and
antecedents of implications, can be instantiated to match the goal.

### Comments

The supplied theorem is pre-processed using `IRULE_CANON`, which removes
the universal quantifiers and antecedents of implications, and
existentially quantifies variables which were instantiated but appeared
only in the antecedents of implications.

Then `MATCH_MP_TAC` or `MATCH_ACCEPT_TAC` is applied (depending on
whether or not the result of the preprocessing is an implication). To
avoid preprocessing entirely, one can use `prim_irule`.

### Example

With goal `R a (f b)` and theorem `thm` being

``` hol4
   |- !x u. P u x ==> !w y. Q w x y ==> R x (f y)
```

the proof step `e (irule thm)` gives new goal
`(?u. P u a) /\ ?w. Q w a b`.

With goal `a = b` and theorem `trans`

``` hol4
   |- !x y. (x = y) ==> !z. (y = z) ==> (x = z)
```

the proof step `e (irule trans)` gives new goal

``` hol4
   ?y. (a = y) /\ (y = b)
```

### See also

[`Tactic.irule_at`](#Tactic.irule_at),
[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC),
[`Tactic.prim_irule`](#Tactic.prim_irule),
[`Drule.IRULE_CANON`](#Drule.IRULE_CANON)
