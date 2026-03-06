## `cv_trans_pre`

``` hol4
cv_transLib.cv_trans_pre : string -> thm -> thm
```

------------------------------------------------------------------------

Translates functional definitions to the `cv_compute` subset of HOL.

Accepts a theorem describing a functional definition. Attempts to
translate this to a function operating over the `:cv` type, used by
`cv_computeLib.cv_compute`. Returns a precondition representing the
proof obligation which must be discharged before this translated
function can be evaluated with `cv_transLib.cv_eval`.

### Failure

When the translation does not produce a precondition, or encounters a
sub-term containing a constant that has not already been translated, or
`cv_transLib.cv_termination_tac` fails to prove the termination goal of
the translator-defined `:cv` function.

### Example

``` hol4
> cv_trans_pre "HD_pre" listTheory.HD;
Finished translating HD, stored in cv_HD_thm

WARNING: definition of cv_HD has a precondition.
You can set up the precondition proof as follows:

Theorem HD_pre[cv_pre]:
  ∀v. HD_pre v
Proof
  ho_match_mp_tac HD_ind (* for example *)
  ...
QED

val it = ⊢ ∀v. HD_pre v ⇔ (∃t h. v = h::t) ∧ v ≠ []: thm
```

### Comments

Designed to produce definitions suitable for evaluation by
`cv_transLib.cv_eval`.

### See also

[`cv_transLib.cv_trans`](#cv_transLib.cv_trans),
[`cv_transLib.cv_trans_pre_rec`](#cv_transLib.cv_trans_pre_rec),
[`cv_transLib.cv_trans_rec`](#cv_transLib.cv_trans_rec),
[`cv_transLib.cv_auto_trans`](#cv_transLib.cv_auto_trans),
[`cv_transLib.cv_auto_trans_pre`](#cv_transLib.cv_auto_trans_pre),
[`cv_transLib.cv_auto_trans_pre_rec`](#cv_transLib.cv_auto_trans_pre_rec),
[`cv_transLib.cv_auto_trans_rec`](#cv_transLib.cv_auto_trans_rec),
[`cv_transLib.cv_eval`](#cv_transLib.cv_eval),
[`cv_transLib.cv_termination_tac`](#cv_transLib.cv_termination_tac)
