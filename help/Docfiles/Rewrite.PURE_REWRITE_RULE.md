## `PURE_REWRITE_RULE`

``` hol4
Rewrite.PURE_REWRITE_RULE : (thm list -> thm -> thm)
```

------------------------------------------------------------------------

Rewrites a theorem with only the given list of rewrites.

This rule provides a method for rewriting a theorem with the theorems
given, and excluding simplification with tautologies in
`implicit_rewrites`. Matching subterms are found recursively starting
from the term in the conclusion part of the theorem, until no more
matches are found. For more details on rewriting see `GEN_REWRITE_RULE`.

`PURE_REWRITE_RULE` is useful when the simplifications that arise by
rewriting a theorem with `implicit_rewrites` are not wanted.

### Failure

Does not fail. May result in divergence, in which case
`PURE_ONCE_REWRITE_RULE` can be used.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_ASM_REWRITE_RULE`](#Rewrite.PURE_ASM_REWRITE_RULE),
[`Rewrite.PURE_ONCE_ASM_REWRITE_RULE`](#Rewrite.PURE_ONCE_ASM_REWRITE_RULE),
[`Rewrite.PURE_ONCE_REWRITE_RULE`](#Rewrite.PURE_ONCE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)
