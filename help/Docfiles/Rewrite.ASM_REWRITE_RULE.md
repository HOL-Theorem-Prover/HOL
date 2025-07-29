## `ASM_REWRITE_RULE`

``` hol4
Rewrite.ASM_REWRITE_RULE : thm list -> thm -> thm
```

------------------------------------------------------------------------

Rewrites a theorem including built-in rewrites and the theorem's
assumptions.

`ASM_REWRITE_RULE` rewrites using the tautologies in
`implicit_rewrites`, the given list of theorems, and the set of
hypotheses of the theorem. All hypotheses are used. No ordering is
specified among applicable rewrites. Matching subterms are searched for
recursively, starting with the entire term of the conclusion and
stopping when no rewritable expressions remain. For more details about
the rewriting process, see `GEN_REWRITE_RULE`. To avoid using the set of
basic tautologies, see `PURE_ASM_REWRITE_RULE`.

### Failure

`ASM_REWRITE_RULE` does not fail, but may result in divergence. To
prevent divergence where it would occur, `ONCE_ASM_REWRITE_RULE` can be
used.

### See also

[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.ONCE_ASM_REWRITE_RULE`](#Rewrite.ONCE_ASM_REWRITE_RULE),
[`Rewrite.PURE_ASM_REWRITE_RULE`](#Rewrite.PURE_ASM_REWRITE_RULE),
[`Rewrite.PURE_ONCE_ASM_REWRITE_RULE`](#Rewrite.PURE_ONCE_ASM_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)
