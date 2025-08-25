## `PURE_ONCE_ASM_REWRITE_RULE`

``` hol4
Rewrite.PURE_ONCE_ASM_REWRITE_RULE : (thm list -> thm -> thm)
```

------------------------------------------------------------------------

Rewrites a theorem once, including the theorem's assumptions as
rewrites.

`PURE_ONCE_ASM_REWRITE_RULE` excludes the basic tautologies in
`implicit_rewrites` from the theorems used for rewriting. It searches
for matching subterms once only, without recursing over already
rewritten subterms. For a general introduction to rewriting tools see
`GEN_REWRITE_RULE`.

### Failure

`PURE_ONCE_ASM_REWRITE_RULE` does not fail and does not diverge.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.ONCE_ASM_REWRITE_RULE`](#Rewrite.ONCE_ASM_REWRITE_RULE),
[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_ASM_REWRITE_RULE`](#Rewrite.PURE_ASM_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)
