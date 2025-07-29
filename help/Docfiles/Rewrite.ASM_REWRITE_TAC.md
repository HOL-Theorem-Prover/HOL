## `ASM_REWRITE_TAC`

``` hol4
Rewrite.ASM_REWRITE_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Rewrites a goal using built-in rewrites and the goal's assumptions.

`ASM_REWRITE_TAC` generates rewrites with the tautologies in
`implicit_rewrites`, the set of assumptions, and a list of theorems
supplied by the user. These are applied top-down and recursively on the
goal, until no more matches are found. The order in which the set of
rewrite equations is applied is an implementation matter and the user
should not depend on any ordering. Rewriting strategies are described in
more detail under `GEN_REWRITE_TAC`. For omitting the common
tautologies, see the tactic `PURE_ASM_REWRITE_TAC`. To rewrite with only
a subset of the assumptions use `FILTER_ASM_REWRITE_TAC`.

### Failure

`ASM_REWRITE_TAC` does not fail, but it can diverge in certain
situations. For rewriting to a limited depth, see
`ONCE_ASM_REWRITE_TAC`. The resulting tactic may not be valid if the
applicable replacement introduces new assumptions into the theorem
eventually proved.

### Example

The use of assumptions in rewriting, specially when they are not in an
obvious equational form, is illustrated below:

``` hol4
   - let val asm = [Term `P x`]
         val goal = Term `P x = Q x`
     in
     ASM_REWRITE_TAC[] (asm, goal)
     end;

   val it = ([([`P x`], `Q x`)], fn) : tactic_result

   - let val asm = [Term `~P x`]
         val goal = Term `P x = Q x`
     in
     ASM_REWRITE_TAC[] (asm, goal)
     end;

   val it = ([([`~P x`], `~Q x`)], fn) : tactic_result
```

### See also

[`Rewrite.FILTER_ASM_REWRITE_TAC`](#Rewrite.FILTER_ASM_REWRITE_TAC),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_ASM_REWRITE_TAC`](#Rewrite.PURE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_ASM_REWRITE_TAC`](#Rewrite.PURE_ONCE_ASM_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC),
[`BasicProvers.VAR_EQ_TAC`](#BasicProvers.VAR_EQ_TAC)
