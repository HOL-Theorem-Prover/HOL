## `cv_eval_raw`

``` hol4
cv_transLib.cv_eval_raw : term -> thm
```

------------------------------------------------------------------------

Uses `cv_computeLib` to evaluate closed terms, equipped with
translations from `cv_transLib`.

Like `cv_transLib.cv_eval`, except it omits the potentially expensive
evaluation out of the `:cv` type.

### Failure

Fails in the same ways as `cv_transLib.cv_eval`.

### Example

``` hol4
> cv_trans rich_listTheory.REPLICATE;
Equations stored under "cv_REPLICATE_def".
Induction stored under "cv_REPLICATE_ind".
Finished translating REPLICATE, stored in cv_REPLICATE_thm
val it = (): unit
> cv_eval “REPLICATE 3 (3:num)”;
val it = ⊢ REPLICATE 3 3 = [3; 3; 3]: thm
> cv_eval_raw “REPLICATE 3 (3:num)”;
val it =
   ⊢ REPLICATE 3 3 =
     to_list cv$c2n (Pair (Num 3) (Pair (Num 3) (Pair (Num 3) (Num 0)))): thm
```

### See also

[`cv_transLib.cv_eval`](#cv_transLib.cv_eval)
