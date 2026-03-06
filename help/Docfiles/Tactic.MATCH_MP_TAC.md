## `MATCH_MP_TAC`

``` hol4
Tactic.MATCH_MP_TAC : thm_tactic
```

------------------------------------------------------------------------

Reduces the goal using a supplied implication, with matching.

When applied to a theorem of the form

``` hol4
   A' |- !x1...xn. s ==> !y1...ym. t
```

`MATCH_MP_TAC` produces a tactic that reduces a goal whose conclusion
`t'` is a substitution and/or type instance of `t` to the corresponding
instance of `s`. Any variables free in `s` but not in `t` will be
existentially quantified in the resulting subgoal:

``` hol4
     A ?- !v1...vi. t'
  ======================  MATCH_MP_TAC (A' |- !x1...xn. s ==> !y1...ym. t)
     A ?- ?z1...zp. s'
```

where `z1`, ..., `zp` are (type instances of) those variables among
`x1`, ..., `xn` that do not occur free in `t`. Note that this is not a
valid tactic unless `A'` is a subset of `A`.

### Failure

Fails unless the theorem is an (optionally universally quantified)
implication whose consequent can be instantiated to match the goal. The
generalized variables `v1`, ..., `vi` must occur in `s'` in order for
the conclusion `t` of the supplied theorem to match `t'`.

### Comments

The tactic `irule` builds on `MATCH_MP_TAC`, normalising the input
theorem more aggressively so that it succeeds more often.

### See also

[`ConseqConv.CONSEQ_CONV_TAC`](#ConseqConv.CONSEQ_CONV_TAC),
[`Thm.EQ_MP`](#Thm.EQ_MP), [`Tactic.irule`](#Tactic.irule),
[`Drule.MATCH_MP`](#Drule.MATCH_MP), [`Thm.MP`](#Thm.MP),
[`Tactic.MP_TAC`](#Tactic.MP_TAC)
