## `PURE_REWRITE_TAC`

``` hol4
Rewrite.PURE_REWRITE_TAC : (thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal with only the given list of rewrites.

`PURE_REWRITE_TAC` behaves in the same way as `REWRITE_TAC`, but without
the effects of the built-in tautologies. The order in which the given
theorems are applied is an implementation matter and the user should not
depend on any ordering. For more information on rewriting strategies see
`GEN_REWRITE_TAC`.

### Failure

`PURE_REWRITE_TAC` does not fail, but it can diverge in certain
situations; in such cases `PURE_ONCE_REWRITE_TAC` may be used.

This tactic is useful when the built-in tautologies are not required as
rewrite equations. It is sometimes useful in making more time-efficient
replacements according to equations for which it is clear that no extra
reduction via tautology will be needed. (The difference in efficiency is
only apparent, however, in quite large examples.)

`PURE_REWRITE_TAC` advances goals but solves them less frequently than
`REWRITE_TAC`; to be precise, `PURE_REWRITE_TAC` only solves goals which
are rewritten to `"T"` (i.e. `TRUTH`) without recourse to any other
tautologies.

### Example

It might be necessary, say for subsequent application of an induction
hypothesis, to resist reducing a term `b = T` to `b`.

``` hol4
  - PURE_REWRITE_TAC [] ([], Term `b = T`);
  > val it = ([([], `b = T`)], fn)
     : (term list * term) list * (thm list -> thm)

  - REWRITE_TAC [] ([], Term `b = T`);
  > val it = ([([], `b`)], fn)
     : (term list * term) list * (thm list -> thm)
```

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Rewrite.FILTER_ASM_REWRITE_TAC`](#Rewrite.FILTER_ASM_REWRITE_TAC),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_ASM_REWRITE_TAC`](#Rewrite.PURE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_ASM_REWRITE_TAC`](#Rewrite.PURE_ONCE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_REWRITE_TAC`](#Rewrite.PURE_ONCE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
