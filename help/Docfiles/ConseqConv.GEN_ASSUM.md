## `GEN_ASSUM`

``` hol4
ConseqConv.GEN_ASSUM : term -> thm -> thm
```

------------------------------------------------------------------------

Generalizes the conclusion of a theorem and the hypotheses containing
the same variable.

When applied to a term `x` and a theorem `[A1, A2] |- t`, where `x`
occurs in `A1` but not in `A2`, the inference rule `GEN_ASSUM` returns
the theorem `[!x. A1 x, A2 |- !x. t`. There is no compulsion that `x`
should be free in `t`.

`GEN_ASSUM` is a generalisation of `GEN`. While `GEN` fails, if `x` is
free in an assumption, `GEN_ASSUM` succeeds.

``` hol4
        A1, A2 |- t
   ---------------------    GEN_ASSUM x   [where x is free in A1, but not in A2]
   (!x. A1), A2 |- !x. t
```

### Failure

Fails if `x` is not a variable.

### See also

[`Thm.GEN`](#Thm.GEN)
