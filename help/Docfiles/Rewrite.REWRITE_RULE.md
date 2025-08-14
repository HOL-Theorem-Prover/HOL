## `REWRITE_RULE`

``` hol4
Rewrite.REWRITE_RULE : (thm list -> thm -> thm)
```

------------------------------------------------------------------------

Rewrites a theorem including built-in tautologies in the list of
rewrites.

Rewriting a theorem using `REWRITE_RULE` utilizes as rewrites two sets
of theorems: the tautologies in the ML list `implicit_rewrites` and the
ones supplied by the user. The rule searches top-down and recursively
for subterms which match the left-hand side of any of the possible
rewrites, until none of the transformations are applicable. There is no
ordering specified among the set of rewrites.

Variants of this rule allow changes in the set of equations used:
`PURE_REWRITE_RULE` and others in its family do not rewrite with the
theorems in `implicit_rewrites`. Rules such as `ASM_REWRITE_RULE` add
the assumptions of the object theorem (or a specified subset of these
assumptions) to the set of possible rewrites.

The top-down recursive search for matches may not be desirable, as this
may increase the number of inferences being made or may result in
divergence. In this case other rewriting tools such as
`ONCE_REWRITE_RULE` and `GEN_REWRITE_RULE` can be used, or the set of
theorems given may be reduced.

See `GEN_REWRITE_RULE` for the general strategy for simplifying theorems
in HOL using equational theorems.

### Failure

Does not fail, but may diverge if the sequence of rewrites is
non-terminating.

Used to manipulate theorems by rewriting them with other theorems. While
resulting in high degree of automation, `REWRITE_RULE` can spawn a large
number of inference steps. Thus, variants such as `PURE_REWRITE_RULE`,
or other rules such as `SUBST`, may be used instead to improve
efficiency.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Conv.REWR_CONV`](#Conv.REWR_CONV),
[`Rewrite.REWRITE_CONV`](#Rewrite.REWRITE_CONV),
[`Thm.SUBST`](#Thm.SUBST)
