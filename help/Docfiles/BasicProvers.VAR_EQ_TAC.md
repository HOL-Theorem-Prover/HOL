## `VAR_EQ_TAC`

``` hol4
BasicProvers.VAR_EQ_TAC : tactic
```

------------------------------------------------------------------------

Simplifies a goal using any assumption of the form `v = t` or `t = v`,
where `v` is a variable

`VAR_EQ_TAC` simplifies the goal, including its assumptions, using one
assumption of the form `v = t` or `t = v`, where `v` is a variable which
is not contained in `t`.

In both cases, `v` is replaced throughout by `t`, and the relevant
assumption is deleted.

### Failure

`VAR_EQ_TAC` fails if there are no such assumptions

### See also

[`bossLib.FULL_SIMP_TAC`](#bossLib.FULL_SIMP_TAC),
[`bossLib.ASM_SIMP_TAC`](#bossLib.ASM_SIMP_TAC),
[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC)
