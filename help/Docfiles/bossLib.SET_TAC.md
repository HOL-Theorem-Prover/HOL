## `SET_TAC`

``` hol4
bossLib.SET_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Tactic to automate some routine pred_set theory by reduction to FOL,
using the given theorems as additional assumptions in the search.

`SET_TAC` reduces basic set-theoretic operators (`IN`, `SUBSET`,
`PSUBSET`, `INTER`, `UNION`, `INSERT`, `DELETE`, `REST`, `DISJOINT`,
`BIGINTER`, `BIGUNION`, `IMAGE`, `SING` and `GSPEC`) in the goal to
their definitions in first-order logic (FOL) and then call `METIS_TAC`
to solve it. With `SET_TAC`, many simple set-theoretic results can be
directly proved without finding needed lemmas in `pred_setTheory`.

### Failure

Fails if the underlying resolution machinery (`METIS_TAC`) cannot prove
the goal, or the supplied theorems are not enough for the FOL reduction,
e.g., when there are other set-theoretic operators in the goal.

### Example

A simple theorem about disjoint sets:

``` hol4
Theorem DISJOINT_RESTRICT_L :
  !s t c. DISJOINT s t ==> DISJOINT (s INTER c) (t INTER c)
Proof SET_TAC []
QED
```

`SET_TAC` can only progress the goal to a successful proof of the
(whole) goal or not at all. `SET_RULE` can be used to prove an
intermediate set-theoretic lemma (there is no way to provide extra
lemmas, however).

### Comments

The assumptions of a goal are ignored when `SET_TAC` is applied. To
include assumptions use `ASM_SET_TAC`.

### See also

[`bossLib.ASM_SET_TAC`](#bossLib.ASM_SET_TAC),
[`bossLib.SET_RULE`](#bossLib.SET_RULE),
[`bossLib.METIS_TAC`](#bossLib.METIS_TAC)
