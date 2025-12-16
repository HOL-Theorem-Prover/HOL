## `PMATCH_MP_TAC`

``` hol4
PairRules.PMATCH_MP_TAC : thm_tactic
```

------------------------------------------------------------------------

Reduces the goal using a supplied implication, with matching.

When applied to a theorem of the form

``` hol4
   A' |- !p1...pn. s ==> !q1...qm. t
```

`PMATCH_MP_TAC` produces a tactic that reduces a goal whose conclusion
`t'` is a substitution and/or type instance of `t` to the corresponding
instance of `s`. Any variables free in `s` but not in `t` will be
existentially quantified in the resulting subgoal:

``` hol4
     A ?- !u1...ui. t'
  ======================  PMATCH_MP_TAC (A' |- !p1...pn. s ==> !q1...qm. t)
     A ?- ?w1...wp. s'
```

where `w1`, ..., `wp` are (type instances of) those pairs among `p1`,
..., `pn` having variables that do not occur free in `t`. Note that this
is not a valid tactic unless `A'` is a subset of `A`.

### Failure

Fails unless the theorem is an (optionally paired universally
quantified) implication whose consequent can be instantiated to match
the goal. The generalized pairs `u1`, ..., `ui` must occur in `s'` in
order for the conclusion `t` of the supplied theorem to match `t'`.

### See also

[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC)
