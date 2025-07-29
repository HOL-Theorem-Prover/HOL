## `HO_MATCH_MP_TAC`

``` hol4
Tactic.HO_MATCH_MP_TAC : thm_tactic
```

------------------------------------------------------------------------

Reduces the goal using a supplied implication, with higher-order
matching.

When applied to a theorem of the form

``` hol4
   A' |- !x1...xn. s ==> t
```

`HO_MATCH_MP_TAC` produces a tactic that reduces a goal whose conclusion
`t'` is a substitution and/or type instance of `t` to the corresponding
instance of `s`. Any variables free in `s` but not in `t` will be
existentially quantified in the resulting subgoal:

``` hol4
     A ?- t'
  ======================  HO_MATCH_MP_TAC (A' |- !x1...xn. s ==> t)
     A ?- ?z1...zp. s'
```

where `z1`, ..., `zp` are (type instances of) those variables among
`x1`, ..., `xn` that do not occur free in `t`. Note that this is not a
valid tactic unless `A'` is a subset of `A`.

### Example

The following goal might be solved by case analysis:

``` hol4
  > g `!n:num. n <= n * n`;
```

We can "manually" perform induction by using the following theorem:

``` hol4
  > numTheory.INDUCTION;
  - val it : thm = |- !P. P 0 /\ (!n. P n ==> P (SUC n)) ==> (!n. P n)
```

which is useful with `HO_MATCH_MP_TAC` because of higher-order matching:

``` hol4
  > e(HO_MATCH_MP_TAC numTheory.INDUCTION);
  - val it : goalstack = 1 subgoal (1 total)

  `0 <= 0 * 0 /\ (!n. n <= n * n ==> SUC n <= SUC n * SUC n)`
```

The goal can be finished with `SIMP_TAC arith_ss []`.

### Failure

Fails unless the theorem is an (optionally universally quantified)
implication whose consequent can be instantiated to match the goal.

### See also

[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC),
[`bossLib.Induct_on`](#bossLib.Induct_on), [`Thm.EQ_MP`](#Thm.EQ_MP),
[`Drule.MATCH_MP`](#Drule.MATCH_MP), [`Thm.MP`](#Thm.MP),
[`Tactic.MP_TAC`](#Tactic.MP_TAC),
[`ConseqConv.CONSEQ_CONV_TAC`](#ConseqConv.CONSEQ_CONV_TAC)
