## `cv_eval`

``` hol4
cv_transLib.cv_eval : term -> thm
```

------------------------------------------------------------------------

Uses `cv_computeLib` to evaluate closed terms, equipped with
translations from `cv_transLib`.

Provides a user-friendly interface to `cv_computeLib.cv_compute`, as
long as `cv_transLib` has been used to translate all constants in the
given input term.

### Failure

When the input term contains either free variables or constants which
have not yet been translated.

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

### See also

[`cv_transLib.cv_trans`](#cv_transLib.cv_trans),
[`cv_transLib.cv_trans_pre`](#cv_transLib.cv_trans_pre),
[`cv_transLib.cv_trans_pre_rec`](#cv_transLib.cv_trans_pre_rec),
[`cv_transLib.cv_trans_rec`](#cv_transLib.cv_trans_rec),
[`cv_transLib.cv_auto_trans`](#cv_transLib.cv_auto_trans),
[`cv_transLib.cv_auto_trans_pre`](#cv_transLib.cv_auto_trans_pre),
[`cv_transLib.cv_auto_trans_pre_rec`](#cv_transLib.cv_auto_trans_pre_rec),
[`cv_transLib.cv_auto_trans_rec`](#cv_transLib.cv_auto_trans_rec),
[`cv_transLib.cv_eval_raw`](#cv_transLib.cv_eval_raw),
[`cv_transLib.cv_termination_tac`](#cv_transLib.cv_termination_tac)
