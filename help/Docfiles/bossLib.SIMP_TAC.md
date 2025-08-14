## `SIMP_TAC`

``` hol4
bossLib.SIMP_TAC : simpset -> thm list -> tactic
```

------------------------------------------------------------------------

Simplifies the goal, using the given simpset and the additional theorems
listed.

`SIMP_TAC` adds the theorems of the second argument to the simpset
argument as rewrites and then applies the resulting simpset to the
conclusion of the goal. The exact behaviour of a simpset when applied to
a term is described further in the entry for `SIMP_CONV`.

With simple simpsets, `SIMP_TAC` is similar in effect to `REWRITE_TAC`;
it transforms the conclusion of a goal by using the (equational)
theorems given and those already in the simpset as rewrite rules over
the structure of the conclusion of the goal.

Just as `ASM_REWRITE_TAC` includes the assumptions of a goal in the
rewrite rules that `REWRITE_TAC` uses, `ASM_SIMP_TAC` adds the
assumptions of a goal to the rewrites and then performs simplification.

### Failure

`SIMP_TAC` never fails, though it may diverge.

### Example

`SIMP_TAC` and the `arith_ss` simpset combine to prove quite difficult
seeming goals:

``` hol4
   - val (_, p) = SIMP_TAC arith_ss []
                 ([], Term`P x /\ (x = y + 3) ==> P x /\ y < x`);

   > val p = fn : thm list -> thm

   - p [];
   > val it = |- P x /\ (x = y + 3) ==> P x /\ y < x : thm
```

`SIMP_TAC` is similar to `REWRITE_TAC` if used with just the `bool_ss`
simpset. Here it is used in conjunction with the arithmetic theorem
`GREATER_DEF`, `|- !m n. m > n = n < m`, to advance a goal:

``` hol4
   - SIMP_TAC bool_ss [GREATER_DEF]  ([], Term`T /\ 5 > 4 \/ F`);
   > val it = ([([], `4 < 5`)], fn) : subgoals
```

### Comments

The simplification library is described further in other documentation,
but its full capabilities are still rather opaque.

Simplification is one of the most powerful tactics available to the HOL
user. It can be used both to solve goals entirely or to make progress
with them. However, poor simpsets or a poor choice of rewrites can still
result in divergence, or poor performance.

### See also

[`bossLib.++`](#bossLib..KAL),
[`bossLib.ASM_SIMP_TAC`](#bossLib.ASM_SIMP_TAC),
[`bossLib.std_ss`](#bossLib.std_ss),
[`bossLib.bool_ss`](#bossLib.bool_ss),
[`bossLib.arith_ss`](#bossLib.arith_ss),
[`bossLib.list_ss`](#bossLib.list_ss),
[`bossLib.FULL_SIMP_TAC`](#bossLib.FULL_SIMP_TAC),
[`simpLib.mk_simpset`](#simpLib.mk_simpset),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`bossLib.SIMP_CONV`](#bossLib.SIMP_CONV),
[`simpLib.SIMP_PROVE`](#simpLib.SIMP_PROVE),
[`bossLib.SIMP_RULE`](#bossLib.SIMP_RULE)
