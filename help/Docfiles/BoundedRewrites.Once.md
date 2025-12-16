## `Once`

``` hol4
BoundedRewrites.Once : thm -> thm
```

------------------------------------------------------------------------

Rewriting control.

When used as an argument to the rewriter or simplifier, `Once th` is a
directive saying that `th` should be used at most once in the rewriting
process. This is useful for controlling looping rewrites.

### Failure

Never fails.

### Example

Suppose factorial was defined as follows:

``` hol4
   - val fact_def = Define `fact n = if n=0 then 1 else n * fact (n-1)`;
   Equations stored under "fact_def".
   Induction stored under "fact_ind".
   > val fact_def = |- fact n = (if n = 0 then 1 else n * fact (n - 1)) : thm
```

The theorem `fact_def` is a looping rewrite since the recursive call
`fac (n-1)` matches the left-hand side of `fact_def`. Thus, a naive
application of the simplifier will loop:

``` hol4
   - SIMP_CONV arith_ss [fact_def] ``fact 6``;
   (* looping *)
   > Interrupted.
```

In order to expand the definition of `fact_def`, the following
invocation can be made

``` hol4
   - SIMP_CONV arith_ss [Once fact_def] ``fact 6``;
   > val it = |- fact 6 = 6 * fact 5 : thm
```

### Comments

Use of `Once` does not compose well. For example,

``` hol4
   tac1 THENL [SIMP_TAC std_ss [Once th],
               SIMP_TAC std_ss [Once th]]
```

is not equivalent in behaviour to

``` hol4
   tac1 THEN SIMP_TAC std_ss [Once th].
```

In the first call two rewrites using `th` can occur; in the second, only
one can occur.

### See also

[`BoundedRewrites.Ntimes`](#BoundedRewrites.Ntimes),
[`Tactical.THEN`](#Tactical.THEN),
[`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC),
[`bossLib.RW_TAC`](#bossLib.RW_TAC),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC)
