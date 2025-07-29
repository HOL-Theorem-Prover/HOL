## `ASM_SIMP_RULE`

``` hol4
simpLib.ASM_SIMP_RULE : simpset -> thm list -> thm -> thm
```

------------------------------------------------------------------------

Simplifies a theorem, using the theorem's assumptions as rewrites in
addition to the provided rewrite theorems and simpset.

### Failure

Never fails, but may diverge.

### Example

``` hol4
- ASM_SIMP_RULE bool_ss [] (ASSUME (Term `x = 3`))
> val it =  [.] |- T : thm
```

The assumptions can be used to simplify the conclusion of the theorem.
For example, if the conclusion of a theorem is an implication, the
antecedent together with the hypotheses may help simplify the
conclusion.

### See also

[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV),
[`simpLib.SIMP_RULE`](#simpLib.SIMP_RULE)
