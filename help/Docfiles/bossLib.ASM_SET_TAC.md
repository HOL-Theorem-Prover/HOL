## `ASM_SET_TAC`

``` hol4
bossLib.ASM_SET_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Tactic to automate some routine set theory by reduction to FOL, using
the assumptions and the theorems given.

`ASM_SET_TAC` is identical in behaviour to `SET_TAC` except that it uses
the assumptions of a goal as well as the provided theorems.

### Failure

Fails if the underlying resolution machinery (`METIS_TAC`) cannot prove
the goal, or the supplied theorems (and the assumptions) are not enough
for the FOL reduction.

### See also

[`bossLib.SET_TAC`](#bossLib.SET_TAC),
[`bossLib.SET_RULE`](#bossLib.SET_RULE)
