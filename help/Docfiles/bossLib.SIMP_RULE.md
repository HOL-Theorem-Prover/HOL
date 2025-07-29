## `SIMP_RULE`

``` hol4
bossLib.SIMP_RULE : simpset -> thm list -> thm -> thm
```

------------------------------------------------------------------------

Simplifies the conclusion of a theorem according to the given simpset
and theorem rewrites.

`SIMP_RULE` simplifies the conclusion of a theorem, adding the given
theorems to the simpset parameter as rewrites. The way in which terms
are transformed as a part of simplification is described in the entry
for `SIMP_CONV`.

### Failure

Never fails, but may diverge.

### Example

The following also demonstrates the higher order rewriting possible with
simplification (`FORALL_AND_THM` states
`|- (!x. P x /\ Q x) = (!x. P x) /\ (!x. Q x)`):

``` hol4
- SIMP_RULE bool_ss [boolTheory.FORALL_AND_THM]
            (ASSUME (Term`!x. P (x + 1) /\ R x /\ x < y`));
> val it =  [.] |- (!x. P (x + 1)) /\ (!x. R x) /\ (!x. x < y) : thm
```

### Comments

`SIMP_RULE ss thmlist` is equivalent to
`CONV_RULE (SIMP_CONV ss thmlist)`.

### See also

[`simpLib.ASM_SIMP_RULE`](#simpLib.ASM_SIMP_RULE),
[`bossLib.SIMP_CONV`](#bossLib.SIMP_CONV),
[`bossLib.SIMP_TAC`](#bossLib.SIMP_TAC),
[`bossLib.bool_ss`](#bossLib.bool_ss)
