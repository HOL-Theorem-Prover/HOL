## `REWRITE_CONV`

``` hol4
Rewrite.REWRITE_CONV : (thm list -> conv)
```

------------------------------------------------------------------------

Rewrites a term including built-in tautologies in the list of rewrites.

Rewriting a term using `REWRITE_CONV` utilizes as rewrites two sets of
theorems: the tautologies in the ML list `implicit_rewrites` and the
ones supplied by the user. The rule searches top-down and recursively
for subterms which match the left-hand side of any of the possible
rewrites, until none of the transformations are applicable. There is no
ordering specified among the set of rewrites.

Variants of this conversion allow changes in the set of equations used:
`PURE_REWRITE_CONV` and others in its family do not rewrite with the
theorems in `implicit_rewrites`.

The top-down recursive search for matches may not be desirable, as this
may increase the number of inferences being made or may result in
divergence. In this case other rewriting tools such as
`ONCE_REWRITE_CONV` and `GEN_REWRITE_CONV` can be used, or the set of
theorems given may be reduced.

See `GEN_REWRITE_CONV` for the general strategy for simplifying theorems
in HOL using equational theorems.

### Failure

Does not fail, but may diverge if the sequence of rewrites is
non-terminating.

Used to manipulate terms by rewriting them with theorems. While
resulting in high degree of automation, `REWRITE_CONV` can spawn a large
number of inference steps. Thus, variants such as `PURE_REWRITE_CONV`,
or other rules such as `SUBST_CONV`, may be used instead to improve
efficiency.

### See also

[`Rewrite.GEN_REWRITE_CONV`](#Rewrite.GEN_REWRITE_CONV),
[`Rewrite.ONCE_REWRITE_CONV`](#Rewrite.ONCE_REWRITE_CONV),
[`Rewrite.PURE_REWRITE_CONV`](#Rewrite.PURE_REWRITE_CONV),
[`Conv.REWR_CONV`](#Conv.REWR_CONV),
[`Drule.SUBST_CONV`](#Drule.SUBST_CONV)
