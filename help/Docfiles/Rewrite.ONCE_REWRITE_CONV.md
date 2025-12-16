## `ONCE_REWRITE_CONV`

``` hol4
Rewrite.ONCE_REWRITE_CONV : (thm list -> conv)
```

------------------------------------------------------------------------

Rewrites a term, including built-in tautologies in the list of rewrites.

`ONCE_REWRITE_CONV` searches for matching subterms and applies rewrites
once at each subterm, in the manner specified for `ONCE_DEPTH_CONV`. The
rewrites which are used are obtained from the given list of theorems and
the set of tautologies stored in `implicit_rewrites`. See
`GEN_REWRITE_CONV` for the general method of using theorems to rewrite a
term.

### Failure

`ONCE_REWRITE_CONV` does not fail; it does not diverge.

`ONCE_REWRITE_CONV` can be used to rewrite a term when recursive
rewriting is not desired.

### See also

[`Rewrite.GEN_REWRITE_CONV`](#Rewrite.GEN_REWRITE_CONV),
[`Rewrite.PURE_ONCE_REWRITE_CONV`](#Rewrite.PURE_ONCE_REWRITE_CONV),
[`Rewrite.PURE_REWRITE_CONV`](#Rewrite.PURE_REWRITE_CONV),
[`Rewrite.REWRITE_CONV`](#Rewrite.REWRITE_CONV)
