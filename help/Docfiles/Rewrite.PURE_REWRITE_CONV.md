## `PURE_REWRITE_CONV`

``` hol4
Rewrite.PURE_REWRITE_CONV : (thm list -> conv)
```

------------------------------------------------------------------------

Rewrites a term with only the given list of rewrites.

This conversion provides a method for rewriting a term with the theorems
given, and excluding simplification with tautologies in
`implicit_rewrites`. Matching subterms are found recursively, until no
more matches are found. For more details on rewriting see
`GEN_REWRITE_CONV`.

`PURE_REWRITE_CONV` is useful when the simplifications that arise by
rewriting a theorem with `implicit_rewrites` are not wanted.

### Failure

Does not fail. May result in divergence, in which case
`PURE_ONCE_REWRITE_CONV` can be used.

### See also

[`Rewrite.GEN_REWRITE_CONV`](#Rewrite.GEN_REWRITE_CONV),
[`Rewrite.ONCE_REWRITE_CONV`](#Rewrite.ONCE_REWRITE_CONV),
[`Rewrite.PURE_ONCE_REWRITE_CONV`](#Rewrite.PURE_ONCE_REWRITE_CONV),
[`Rewrite.REWRITE_CONV`](#Rewrite.REWRITE_CONV)
