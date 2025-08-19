## `cv_trans_pre_rec`

``` hol4
cv_transLib.cv_trans_pre_rec : string -> thm -> tactic -> thm
```

------------------------------------------------------------------------

Translates functional definitions to the `cv_compute` subset of HOL.

This function is the same as `cv_transLib.cv_trans_pre`, except that it
also takes a user-provided tactic for proving termination of the
translator-defined `:cv` function.

### Failure

When the translation encounters a sub-term containing a constant that
has not already been translated, or the provided tactic fails to prove
the termination goal of the translator-defined `:cv` function.

### Example

``` hol4
> Definition count_up_def:
    count_up m k = if m < k:num then 1 + count_up (m+1) k else 0:num
  Termination
    WF_REL_TAC ‘measure $ λ(m,k). k - m:num’
  End;
Equations stored under "count_up_def".
Induction stored under "count_up_ind".
val count_up_def =
   ⊢ ∀m k. count_up m k = if m < k then 1 + count_up (m + 1) k else 0: thm
> val cv_count_up_pre = cv_trans_pre_rec "count_pre" count_up_def
    (WF_REL_TAC ‘measure $ λ(m,k). cv$c2n k - cv$c2n m’
     \\ Cases \\ Cases \\ gvs [] \\ rw [] \\ gvs []);
Equations stored under "cv_count_up_def".
Induction stored under "cv_count_up_ind".
Finished translating count_up, stored in cv_count_up_thm

WARNING: definition of cv_count_up has a precondition.
You can set up the precondition proof as follows:

Theorem count_up_pre[cv_pre]:
  ∀m k. count_up_pre m k
Proof
  ho_match_mp_tac count_up_ind (* for example *)
  ...
QED

val cv_count_up_pre =
   ⊢ ∀m k. count_up_pre m k ⇔ m < k ⇒ count_up_pre (m + 1) k: thm
> Theorem count_up_pre[cv_pre]:
    ∀m k. count_up_pre m k
  Proof
    ho_match_mp_tac count_up_ind \\ rw []
    \\ simp [Once cv_count_up_pre]
  QED
val count_up_pre = ⊢ ∀m k. count_up_pre m k: thm
> cv_eval “count_up 5 100”;
val it = ⊢ count_up 5 100 = 95: thm
```

### Comments

Designed to produce definitions suitable for evaluation by
`cv_transLib.cv_eval`.

### See also

[`cv_transLib.cv_trans`](#cv_transLib.cv_trans),
[`cv_transLib.cv_trans_pre`](#cv_transLib.cv_trans_pre),
[`cv_transLib.cv_trans_rec`](#cv_transLib.cv_trans_rec),
[`cv_transLib.cv_auto_trans`](#cv_transLib.cv_auto_trans),
[`cv_transLib.cv_auto_trans_pre`](#cv_transLib.cv_auto_trans_pre),
[`cv_transLib.cv_auto_trans_pre_rec`](#cv_transLib.cv_auto_trans_pre_rec),
[`cv_transLib.cv_auto_trans_rec`](#cv_transLib.cv_auto_trans_rec),
[`cv_transLib.cv_eval`](#cv_transLib.cv_eval),
[`cv_transLib.cv_termination_tac`](#cv_transLib.cv_termination_tac)
