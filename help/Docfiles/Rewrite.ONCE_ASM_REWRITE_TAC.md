## `ONCE_ASM_REWRITE_TAC`

``` hol4
Rewrite.ONCE_ASM_REWRITE_TAC : (thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal once including built-in rewrites and the goal's
assumptions.

`ONCE_ASM_REWRITE_TAC` behaves in the same way as `ASM_REWRITE_TAC`, but
makes one pass only through the term of the goal. The order in which the
given theorems are applied is an implementation matter and the user
should not depend on any ordering. See `GEN_REWRITE_TAC` for more
information on rewriting a goal in HOL.

### Failure

`ONCE_ASM_REWRITE_TAC` does not fail and, unlike `ASM_REWRITE_TAC`, does
not diverge. The resulting tactic may not be valid, if the rewrites
performed add new assumptions to the theorem eventually proved.

### Example

The use of `ONCE_ASM_REWRITE_TAC` to control the amount of rewriting
performed is illustrated below:

``` hol4
   - ONCE_ASM_REWRITE_TAC []
       ([Term` (a:'a) = b`, Term `(b:'a) = c`], Term `P (a:'a): bool`);

   > val it = ([([`a = b`, `b = c`], `P b`)], fn)
      : (term list * term) list * (thm list -> thm)



   - (ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [])
     ([Term`(a:'a) = b`, Term`(b:'a) = c`], Term `P (a:'a): bool`);

   > val it = ([([`a = b`, `b = c`], `P c`)], fn)
      : (term list * term) list * (thm list -> thm)
```

`ONCE_ASM_REWRITE_TAC` can be applied once or iterated as required to
give the effect of `ASM_REWRITE_TAC`, either to avoid divergence or to
save inference steps.

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
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
