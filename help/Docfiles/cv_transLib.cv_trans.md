## `cv_trans`

``` hol4
cv_transLib.cv_trans : thm -> unit
```

------------------------------------------------------------------------

Translates functional definitions to the `cv_compute` subset of HOL.

This function is the same as `cv_transLib.cv_trans_pre`, except that it
tries to discharge any preconditions automatically.

### Failure

When translation produces a precondition that `cv_transLib.cv_trans`
cannot prove automatically, or encounters a sub-term containing a
constant that has not already been translated, or
`cv_transLib.cv_termination_tac` fails to prove the termination goal of
the translator-defined `:cv` function. In the latter case, the
termination goal is pushed onto the goal stack.

### Example

``` hol4
> cv_trans arithmeticTheory.FACT;
Equations stored under "cv_FACT_def".
Induction stored under "cv_FACT_ind".
Finished translating FACT, stored in cv_FACT_thm
val it = (): unit
> cv_eval “FACT 50”;
val it =
   ⊢ FACT 50 =
     30414093201713378043612608166064768844377641568960512000000000000: thm
```

### Comments

Designed to produce definitions suitable for evaluation by
`cv_transLib.cv_eval`.

### See also

[`cv_transLib.cv_trans_pre`](#cv_transLib.cv_trans_pre),
[`cv_transLib.cv_trans_pre_rec`](#cv_transLib.cv_trans_pre_rec),
[`cv_transLib.cv_trans_rec`](#cv_transLib.cv_trans_rec),
[`cv_transLib.cv_auto_trans`](#cv_transLib.cv_auto_trans),
[`cv_transLib.cv_auto_trans_pre`](#cv_transLib.cv_auto_trans_pre),
[`cv_transLib.cv_auto_trans_pre_rec`](#cv_transLib.cv_auto_trans_pre_rec),
[`cv_transLib.cv_auto_trans_rec`](#cv_transLib.cv_auto_trans_rec),
[`cv_transLib.cv_eval`](#cv_transLib.cv_eval),
[`cv_transLib.cv_termination_tac`](#cv_transLib.cv_termination_tac)
